(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, THE ROOM COUNT OF THE TRACE CARRIER P'' (a Theorem Labs lane's ruling 22:03Z, item 5;
   design: a Theorem Labs lane's internal file WILD-COUNT.md). rule 24: no function proved. rule 24: proves no function (kind:
   engine statements and laws over YG01.v's wild_part / admits and YCbqG.v's journal budget).

   WHAT BOUNDS THE WILD TRACES. The journal's last conjunct (YCbqG.v ajournal_xw) says that the wild traces stored at
   the current state are those stored at the function's entry plus at most the budget WS:
     incl (wild_part U (st_depot S')) (wild_part U (st_depot S) ++ WS).
   The depot holds no repeat (YG01.v depot_fits, first conjunct; the cf instance gives it as wfc_depot of amc_wf; at an
   abstract ARx it is AR_laws_x's field 25, alx_depot_nodup), so
   the inclusion is a COUNT: |wild_part U d'| <= |wild_part U d| + |WS| (ajournal_xw_wild_count). A budget may repeat a
   trace (a cursor free made a thousand times puts its one trace in WS a thousand times), so the count is stated
   against a SET of known traces and a number of FRESH ones: wfresh set WS counts the budget's traces outside set.

   1. LISTS (no journal): wild_part_NoDup, wild_len_incl, wild_count, wild_count_set; the budget measure wild_fresh /
      wfresh and its laws, wbudget_app (budgets of calls in a row add); admits_of_count (admits from room),
      admits_of_budget.
   2. THE ROOM a text states at entry: wild_room U set k d - the wild traces of d, the set and k more fit in u_wmax.
      wild_room_admits gives admits at every call whose trace is in set or that has a fresh slot left; wild_room_step
      carries the room across any stretch that stored a budget ws (k drops by wfresh set ws); wild_room_set turns
      fresh slots into a set's reservations, wild_room_unset a set's reservations into counted traces (a callee's set
      is paid from its caller's fresh slots); wild_room_of_count / wild_room_count convert. The satisfiability
      witnesses: wild_room_init (the empty start-up depot, YG00.v init_state), wild_room_fixed (a depot of fixed
      traces only, the driver's before the first entry call), wild_room_cw / wild_room_cw_fix (a cursor set CW whose
      traces are the only wild ones stored), and their image-free parts K_LLVMF (= 140), init_depot_nil,
      wild_room_init_K, wild_room_run_fits, cw_of, wild_room_cw_init, wild_room_cw_stored. The instances are one file
      per image, each Requiring only its own image's universe: lib/A/WildRoomInstA.v (A') and lib/AU/WildRoomInstB.v
      (B'). The negative controls: wild_room_too_big (a room that does not fit is false) and
      wild_room_cursor_countermodel (a Theorem Labs lane's cursor-free countermodel violates the cursor texts' room premise);
      per image wild_room_R1_A / wild_room_R1_B. inU_unwind_wild: clause 4b admits a trace with a wild two-word
      prefix whatever its later words (per image tx_trace_inU_A / _B with the negatives tx_trace_neg_A / _B).
   3. A SEQUENCE OF STRETCHES (the driver's entry calls, or any walk's calls in a row): wild_steps, steps_end,
      steps_budget; wild_steps_incl, wild_steps_count, wild_steps_uniform, wild_room_steps, and wild_room_run (the run
      starts with an empty depot, YG00.v init_state: N entry calls of budget K each fit when N * K <= u_wmax).
   4. THE JOURNAL (Section j over YCbqG.v's ajournal_xw): ajournal_xw_wild_count, ajournal_xw_wild_count_set,
      ajournal_xw_room, ajournal_xw_admits (the walk's admission of an allocator call from its entry room and its
      journal so far), ajournal_xw_norm (a budget replaced by its set part and its fresh part). With LAWS (Section l),
      wild_room_admits_laws / ajournal_xw_admits_laws are wild_room_admits / ajournal_xw_admits with the depot's NoDup
      premise taken from AR_laws_x's field 25 (alx_depot_nodup) at the call's ARx state.
      ajournal_xw_rebase / ajournal_xw_unbase / ajournal_xw_unbase0: a journal at a NON-EMPTY budget is one at the
      empty budget from the entry state with its depot moved to the current one (set_depot, YG00.v; no other journal
      conjunct reads the entry depot). So EVERY call rule stated at the empty budget (YCbqGcall.v, YCbqGcallW.v,
      YGcallSnp.v ...) serves a caller at any budget: rebase, apply the rule, unbase. afn_pre_x_at_w is YCbqG.v's
      afn_pre_x_at at any budget.
      ajournal_xw_rebase / ajournal_xw_unbase make EVERY existing call rule work unchanged for a callee of budget 0
      (no wild site in its subtree), so no existing rule and no text without a wild site changes: only the texts whose
      subtree can store a wild trace change (their posts become the budgeted ones of part 5).
   5. BUDGETED CALLEES (Section l): a text whose subtree may store a wild trace states its post with the journal at a
      budget it chooses, of which it states P WS (P = wbudget set k: at most k traces outside set). The posts are
      apost_base_xb / apost_base_xbF (YCbqG.v apost_base_x / apost_base_xF) and fpostW_xb / fpostWF_xb (YCbqGcallW.v
      fpostW_x / fpostWF_x), each the old post with `exists WS, P WS /\` the journal at WS; the old post is the new one
      at any P with P [] (apost_base_xb_of_x, ..). The call rules aj_call_xb_sp, aj_call_xbF(_sp), aj_call_xWb(_sp),
      aj_call_xWFb(_sp) are YCbqGcall.v's aj_call_x_sp / aj_call_xF(_sp) and YCbqGcallW.v's aj_call_xW(_sp) /
      aj_call_xWF(_sp) with the caller's journal at any budget WS0, the callee's post budgeted, and the caller's journal
      after the call at WS0 ++ WS1 (YCbqG.v ajournal_xw_sub). fpostW_xb_of_kept / fpostWF_xb_of_kept close a budgeted
      caller-window walk as YCbqGcallW.v's fpostW_x_of_kept / fpostWF_x_of_kept close a plain one.
   Numerals: 0, 1 (counts), 16 (stack alignment), 4096 (cgif's lowest block address), 16384 (ASTACK) and 2 ^ 64 are
   LENGTH / DERIVED constants of the rules copied; register numbers 1, 2, 3, 4 are WORD. No address literal. *)
(* Modified by Theorem Labs, 2026-10: parts 4 and 5 over a world relation R (suffix R). A free or realloc of a live
   block can hide shadow again, so a walk that crosses one proves YA0nH.SRrG at a relation wider than wle with its
   journal at that relation (YCbqG.v ajournal_xwR / ajournal_xR). Every lemma of part 4 that carries a journal, and
   apost_base_xb_of_x .. fpostWF_xb_of_kept, has an R form that takes R first (no law of R is used); the call rules
   aj_call_xb_spR, aj_call_xbF_spR, aj_call_xbFR, aj_call_xWbR, aj_call_xWb_spR, aj_call_xWFbR, aj_call_xWFb_spR take
   R and its two laws (reflexive, transitive) first, then the plain rule's binders, with the journals, the callee's
   post (apost_base_xbR / apost_base_xbFR / fpostW_xbR / fpostWF_xbR) and the conclusion at R; the composition is
   YCbqG.v's ajournal_xw_subR. Each plain lemma is its R form at wle (wle_refl / wle_trans); its statement is
   unchanged. aj_call_x_sp_w and aj_call_xb are removed: no code outside this file used them. fpostW_xb_R_lift: a
   plain fpostW_xb (journal at wle) is fpostW_xbR at every R that contains wle. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbq YK0o YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ============================================================================ *)
(* 1. LISTS                                                                      *)
(* the depot holds no repeat, so neither does its wild part *)
Lemma wild_part_NoDup : forall U d, List.NoDup d -> List.NoDup (wild_part U d).
Proof. intros U d H. unfold wild_part. apply NoDup_filter. exact H. Qed.
(* the start-up depot (YG00.v init_state: st_depot = []) holds no wild trace *)
Lemma wild_part_nil : forall U, wild_part U [] = [].
Proof. reflexivity. Qed.
(* a list without repeats inside b ++ ws has at most |b| + |ws| entries *)
Lemma wild_len_incl : forall (a b ws : list (list Z)), List.NoDup a -> incl a (b ++ ws) ->
  (length a <= length b + length ws)%nat.
Proof. intros a b ws Hn Hi. rewrite <- length_app. exact (NoDup_incl_length Hn Hi). Qed.
(* THE COUNT of a stretch: the wild traces stored after it number at most those before it plus its budget *)
Lemma wild_count : forall U d d' ws, List.NoDup d' -> incl (wild_part U d') (wild_part U d ++ ws) ->
  (length (wild_part U d') <= length (wild_part U d) + length ws)%nat.
Proof. intros U d d' ws Hn Hi. exact (wild_len_incl _ _ _ (wild_part_NoDup U d' Hn) Hi). Qed.

(* THE BUDGET MEASURE: the traces of a budget ws outside a set of known traces (fresh ones), and their number *)
Definition wild_fresh (set ws : list (list Z)) : list (list Z) := List.filter (fun t => negb (mem_trace t set)) ws.
Definition wfresh (set ws : list (list Z)) : nat := length (wild_fresh set ws).
(* the budget predicate of a budgeted post: at most k traces outside set *)
Definition wbudget (set : list (list Z)) (k : nat) (ws : list (list Z)) : Prop := (wfresh set ws <= k)%nat.
Lemma wild_fresh_cover : forall set ws, incl ws (set ++ wild_fresh set ws).
Proof.
intros set ws t Ht. apply in_or_app. destruct (mem_trace t set) eqn:Em.
- left. apply mem_trace_In. exact Em.
- right. unfold wild_fresh. apply filter_In. split; [exact Ht|]. cbv beta. rewrite Em. reflexivity.
Qed.
Lemma wfresh_nil_set : forall ws, wfresh [] ws = length ws.
Proof. intros ws. unfold wfresh, wild_fresh. induction ws as [|t ws IH]; cbn in *; congruence. Qed.
Lemma wfresh_app : forall set ws1 ws2, wfresh set (ws1 ++ ws2) = (wfresh set ws1 + wfresh set ws2)%nat.
Proof. intros set ws1 ws2. unfold wfresh, wild_fresh. rewrite filter_app, length_app. reflexivity. Qed.
Lemma wfresh_le : forall set ws, (wfresh set ws <= length ws)%nat.
Proof.
intros set ws. unfold wfresh, wild_fresh. induction ws as [|t ws IH]; [cbn; lia|].
cbn. destruct (negb (mem_trace t set)); cbn; lia.
Qed.
(* a call trace in the set costs nothing; any call trace costs at most one *)
Lemma wfresh_one_in : forall set tr, In tr set -> wfresh set [tr] = 0%nat.
Proof.
intros set tr H. apply mem_trace_In in H. unfold wfresh, wild_fresh. cbn. rewrite H. reflexivity.
Qed.
Lemma wfresh_one : forall set tr, (wfresh set [tr] <= 1)%nat.
Proof. intros set tr. pose proof (wfresh_le set [tr]) as H. exact H. Qed.
Lemma wfresh_incl : forall set ws, incl ws set -> wfresh set ws = 0%nat.
Proof.
intros set ws H. unfold wfresh, wild_fresh. induction ws as [|t ws IH]; [reflexivity|].
assert (Et : mem_trace t set = true) by (apply mem_trace_In; apply H; left; reflexivity).
cbn. rewrite Et. cbn. apply IH. intros x Hx. apply H. right. exact Hx.
Qed.
Lemma wfresh_zero_incl : forall set ws, wfresh set ws = 0%nat -> incl ws set.
Proof.
intros set ws H t Ht. destruct (in_app_or _ _ _ (wild_fresh_cover set ws t Ht)) as [H1|H1]; [exact H1|].
unfold wfresh in H. apply length_zero_iff_nil in H. rewrite H in H1. destruct H1.
Qed.
(* the count against a set and a fresh number: repeats of known traces cost nothing *)
Lemma wild_count_set : forall U d d' set ws, List.NoDup d' -> incl (wild_part U d') (wild_part U d ++ ws) ->
  (length (wild_part U d') <= length (wild_part U d) + length set + wfresh set ws)%nat.
Proof.
intros U d d' set ws Hn Hi.
pose proof (wild_len_incl _ _ _ (wild_part_NoDup U d' Hn) (wild_incl_mono _ _ _ _ (wild_fresh_cover set ws) Hi)) as L.
rewrite length_app in L. unfold wfresh. lia.
Qed.
(* the budgets of calls in a row add (a caller's post: its callees' budgets appended) *)
Lemma wbudget_app : forall set k1 k2 ws1 ws2, wbudget set k1 ws1 -> wbudget set k2 ws2 ->
  wbudget set (k1 + k2) (ws1 ++ ws2).
Proof. intros set k1 k2 ws1 ws2 H1 H2. unfold wbudget in *. rewrite wfresh_app. lia. Qed.

(* THE ADMISSION from room (YG01.v admits, its third arm): a trace of depot shape is admitted when the wild part has
   room for one more *)
Lemma admits_of_count : forall U tr s, (length (wild_part U (st_depot s)) < u_wmax U)%nat -> inU U tr -> admits U tr s.
Proof. intros U tr s Hlt Hi. split; [exact Hi|]. right. right. exact Hlt. Qed.
(* ... and so after a stretch of budget ws from a depot d0 that left room for ws and one more *)
Lemma admits_of_budget : forall U tr s d0 ws, List.NoDup (st_depot s) ->
  incl (wild_part U (st_depot s)) (wild_part U d0 ++ ws) ->
  (length (wild_part U d0) + length ws < u_wmax U)%nat -> inU U tr -> admits U tr s.
Proof.
intros U tr s d0 ws Hn Hi Hlt Htr. apply admits_of_count; [|exact Htr].
pose proof (wild_count U d0 (st_depot s) ws Hn Hi) as L. lia.
Qed.

(* ============================================================================ *)
(* 2. THE ROOM a text states at its entry: the wild traces of d, every trace of set and k more fit in u_wmax.
   b is any list that covers the wild part beside set (at entry: the wild part itself, wild_room_of_count). *)
Definition wild_room (U : Univ) (set : list (list Z)) (k : nat) (d : list (list Z)) : Prop :=
  exists b, incl (wild_part U d) (b ++ set) /\ (length b + length set + k <= u_wmax U)%nat.
Lemma wild_room_of_count : forall U set k d, (length (wild_part U d) + length set + k <= u_wmax U)%nat ->
  wild_room U set k d.
Proof. intros U set k d H. exists (wild_part U d). split; [apply incl_appl, incl_refl | exact H]. Qed.
Lemma wild_room_count : forall U set k d, List.NoDup d -> wild_room U set k d ->
  (length (wild_part U d) + k <= u_wmax U)%nat.
Proof.
intros U set k d Hn (b & Hi & Hb). pose proof (wild_len_incl _ _ _ (wild_part_NoDup U d Hn) Hi) as L. lia.
Qed.
Lemma wild_room_le : forall U set k k' d, (k' <= k)%nat -> wild_room U set k d -> wild_room U set k' d.
Proof. intros U set k k' d Hk (b & Hi & Hb). exists b. split; [exact Hi | lia]. Qed.
(* a set's reservations as wild traces already counted (unset), and fresh slots as a set's reservations (set) *)
Lemma wild_room_unset : forall U set k d, wild_room U set k d -> wild_room U [] k d.
Proof.
intros U set k d (b & Hi & Hb). exists (b ++ set). split; [rewrite app_nil_r; exact Hi|].
rewrite length_app. cbn [length]. lia.
Qed.
Lemma wild_room_set : forall U set k d, wild_room U [] (length set + k) d -> wild_room U set k d.
Proof.
intros U set k d (b & Hi & Hb). exists b. rewrite app_nil_r in Hi. split; [apply incl_appl; exact Hi|].
cbn [length] in Hb. lia.
Qed.
(* THE ADMISSION from room: a call whose trace is in the set, or that has a fresh slot left, is admitted *)
Lemma wild_room_admits : forall U set k s tr, List.NoDup (st_depot s) -> wild_room U set k (st_depot s) ->
  inU U tr -> In tr set \/ (0 < k)%nat -> admits U tr s.
Proof.
intros U set k s tr Hnd (b & Hi & Hb) Htr Hc. split; [exact Htr|].
destruct (mem_trace tr (st_depot s)) eqn:Em; [left; reflexivity|].
destruct (mem_trace tr (u_fix U)) eqn:Ef; [right; left; reflexivity|].
right. right. pose proof (wild_part_NoDup U _ Hnd) as Hwn.
destruct Hc as [Hin | Hk].
- assert (Hrm : incl (wild_part U (st_depot s)) (List.remove (list_eq_dec Z.eq_dec) tr (b ++ set))).
  { intros t Ht. apply in_in_remove.
    - intros ->. apply wild_part_In in Ht as [Ht _]. apply mem_trace_In in Ht. congruence.
    - exact (Hi t Ht). }
  pose proof (NoDup_incl_length Hwn Hrm) as L1.
  assert (L2 : (length (List.remove (list_eq_dec Z.eq_dec) tr (b ++ set)) < length (b ++ set))%nat).
  { apply remove_length_lt. apply in_or_app. right. exact Hin. }
  rewrite length_app in L2. lia.
- pose proof (wild_len_incl _ _ _ Hwn Hi) as L1. lia.
Qed.
(* THE ROOM ACROSS A STRETCH that stored at most the budget ws: the fresh traces of ws use fresh slots *)
Lemma wild_room_step : forall U set k d d' ws, wild_room U set k d ->
  incl (wild_part U d') (wild_part U d ++ ws) -> (wfresh set ws <= k)%nat ->
  wild_room U set (k - wfresh set ws) d'.
Proof.
intros U set k d d' ws (b & Hi & Hb) Hw Hk. exists (b ++ wild_fresh set ws). split.
- intros t Ht. destruct (in_app_or _ _ _ (Hw t Ht)) as [H|H].
  + destruct (in_app_or _ _ _ (Hi t H)) as [H1|H1].
    * apply in_or_app. left. apply in_or_app. left. exact H1.
    * apply in_or_app. right. exact H1.
  + destruct (in_app_or _ _ _ (wild_fresh_cover set ws t H)) as [H1|H1].
    * apply in_or_app. right. exact H1.
    * apply in_or_app. left. apply in_or_app. right. exact H1.
- rewrite length_app. unfold wfresh in *. lia.
Qed.
(* THE SATISFIABILITY WITNESSES of the room conjunct. At start-up the depot is empty (YG00.v init_state). *)
Lemma wild_room_init : forall U set k, (length set + k <= u_wmax U)%nat -> wild_room U set k [].
Proof. intros U set k H. apply wild_room_of_count. rewrite wild_part_nil. cbn [length]. lia. Qed.
(* a depot whose every trace is fixed (the driver's traces before the first entry call) has no wild trace *)
Lemma wild_room_fixed : forall U set k d, (forall t, In t d -> In t (u_fix U)) ->
  (length set + k <= u_wmax U)%nat -> wild_room U set k d.
Proof.
intros U set k d Hf H. exists []. split; [|cbn [length]; lia].
intros t Ht. exfalso. apply wild_part_In in Ht as [Ht Hm].
pose proof (proj2 (mem_trace_In t (u_fix U)) (Hf t Ht)) as E. congruence.
Qed.
(* a cursor set CW whose traces are the only wild ones stored: the room for CW with no fresh slot *)
Lemma wild_room_cw : forall U CW d, incl (wild_part U d) CW -> (length CW <= u_wmax U)%nat -> wild_room U CW 0 d.
Proof. intros U CW d Hi H. exists []. split; [exact Hi | cbn [length]; lia]. Qed.
(* every stored trace fixed or one of CW's: then CW's traces are the only wild ones stored *)
Lemma wild_room_cw_fix : forall U CW d, (forall t, In t d -> In t (u_fix U) \/ In t CW) ->
  (length CW <= u_wmax U)%nat -> wild_room U CW 0 d.
Proof.
intros U CW d Hd H. apply wild_room_cw; [|exact H].
intros t Ht. apply wild_part_In in Ht as [Ht Hm]. destruct (Hd t Ht) as [E|E]; [|exact E].
exfalso. apply mem_trace_In in E. congruence.
Qed.
(* THE IMAGE-FREE PART OF THE INSTANCE WITNESSES (lib/A/WildRoomInstA.v, lib/AU/WildRoomInstB.v): the room of one
   LLVMFuzzerTestOneInput call (the internal file WILD-COUNT.md section 7, LIB_WILD_BUDGET), the start state's depot (YG00.v
   init_state is the driver's allocator state at entry on both images), and the cursor set of a pj_parse call built
   from an image's first two wild prefixes (Tfib_wild: parse_items' free, then parse_string's) and the two words the
   unwinder reads. *)
Definition K_LLVMF : nat := 140.
Lemma init_depot_nil : st_depot init_state = [].
Proof. reflexivity. Qed.
Lemma wild_room_init_K : forall U, (K_LLVMF <= u_wmax U)%nat -> wild_room U [] K_LLVMF (st_depot init_state).
Proof. intros U H. rewrite init_depot_nil. apply wild_room_init. cbn [length]. exact H. Qed.
(* room for the driver's at most 4 entry calls is room for one *)
Lemma wild_room_run_fits : forall w, (4 * K_LLVMF <= w)%nat -> (K_LLVMF <= w)%nat.
Proof. intros w H. unfold K_LLVMF in *. lia. Qed.
Definition cw_of (Wl : list (list Z)) (w1 w2 : Z) : list (list Z) :=
  [List.nth 0 Wl [] ++ [w1]; List.nth 1 Wl [] ++ [w2]].
Lemma cw_of_length : forall Wl w1 w2, length (cw_of Wl w1 w2) = 2%nat.
Proof. reflexivity. Qed.
(* CW not stored yet, at the start state; and both of CW's traces stored *)
Lemma wild_room_cw_init : forall U CW, (length CW <= u_wmax U)%nat -> wild_room U CW 0 (st_depot init_state).
Proof. intros U CW H. apply wild_room_cw_fix; [rewrite init_depot_nil; intros t [] | exact H]. Qed.
Lemma wild_room_cw_stored : forall U CW, (length CW <= u_wmax U)%nat -> wild_room U CW 0 CW.
Proof. intros U CW H. apply wild_room_cw_fix; [intros t Ht; right; exact Ht | exact H]. Qed.
(* NEGATIVE CONTROLS of the room premise (a Theorem Labs lane's ruling 00:43Z on the cursor texts): the room bites. A text's
   room for a set and k fresh slots is false when they do not fit (wild_room_too_big). a Theorem Labs lane's countermodel to
   the state-keyed cursor-free premise (a universe with room for ONE wild trace, two cursor frees with data words
   w1 <> w2) violates exactly the cursor texts' room premise: its CW has two traces and u_wmax is 1. *)
Lemma wild_room_too_big : forall U set k d, (u_wmax U < length set + k)%nat -> ~ wild_room U set k d.
Proof. intros U set k d H [b [_ Hb]]. lia. Qed.
Lemma wild_room_cursor_countermodel : forall pc r w1 w2,
  ~ wild_room (MkUniv [] [[pc; r]] 1) [[pc; r; w1]; [pc; r; w2]] 0 [].
Proof. intros pc r w1 w2. apply wild_room_too_big. cbn. lia. Qed.
(* CLAUSE 4b ADMITS ANY TAIL (C-TXTRACE): an unwinder trace whose first two words are a wild
   prefix is in the universe whatever the later words are, including a word the unwinder reads from a stack slot the
   program never wrote (round_trip_text's s1 + 8). The length side is unwind_of_chain's firstn kUnwindMax. *)
Lemma inU_unwind_wild : forall U pc0 a ra b ch, ra <> pc0 -> In [pc0; ra] (u_wild U) ->
  inU U (unwind_of_chain pc0 ((a, ra, b) :: ch)).
Proof.
intros U pc0 a ra b ch Hne Hw. unfold inU, unwind_of_chain. split.
- rewrite firstn_length. lia.
- right. unfold wild_shape. cbn [flat_map]. rewrite (proj2 (Z.eqb_neq ra pc0) Hne).
  exists [pc0; ra], (firstn (kUnwindMax - 2) (flat_map (fun r => match r with (_, ra0, _) => if ra0 =? pc0 then [] else [ra0] end) ch)).
  split; [exact Hw | reflexivity].
Qed.

(* ============================================================================ *)
(* 3. A SEQUENCE OF STRETCHES: each step (ws, d') stores at most ws from the previous depot to d' *)
Fixpoint wild_steps (U : Univ) (d : list (list Z)) (st : list (list (list Z) * list (list Z))) : Prop :=
  match st with
  | [] => True
  | (ws, d') :: r => incl (wild_part U d') (wild_part U d ++ ws) /\ wild_steps U d' r
  end.
Fixpoint steps_end (d : list (list Z)) (st : list (list (list Z) * list (list Z))) : list (list Z) :=
  match st with [] => d | (_, d') :: r => steps_end d' r end.
Definition steps_budget (st : list (list (list Z) * list (list Z))) : list (list Z) := List.concat (map fst st).
Lemma wild_steps_incl : forall U st d, wild_steps U d st ->
  incl (wild_part U (steps_end d st)) (wild_part U d ++ steps_budget st).
Proof.
intros U st. unfold steps_budget. induction st as [|[ws d'] r IH]; intros d H.
- cbn. rewrite app_nil_r. apply incl_refl.
- cbn [wild_steps] in H. destruct H as [H1 H2]. cbn [steps_end List.map List.concat].
  exact (wild_incl_trans _ _ _ _ _ (IH d' H2) H1).
Qed.
Lemma wild_steps_count : forall U st d, wild_steps U d st -> List.NoDup (steps_end d st) ->
  (length (wild_part U (steps_end d st)) <= length (wild_part U d) + length (steps_budget st))%nat.
Proof. intros U st d Hs Hn. exact (wild_count _ _ _ _ Hn (wild_steps_incl U st d Hs)). Qed.
Lemma steps_budget_length : forall st, length (steps_budget st) = List.list_sum (map (fun p => length (fst p)) st).
Proof.
unfold steps_budget. induction st as [|[ws d'] r IH]; [reflexivity|].
cbn [List.map List.concat List.list_sum fst]. rewrite length_app, IH. reflexivity.
Qed.
Lemma steps_budget_le : forall st K, List.Forall (fun p => (length (fst p) <= K)%nat) st ->
  (length (steps_budget st) <= length st * K)%nat.
Proof.
intros st K HF. unfold steps_budget. induction HF as [|[ws d'] r Hx HF IH]; [cbn; lia|].
cbn [List.map List.concat length Nat.mul fst] in *. rewrite length_app. lia.
Qed.
(* N steps of budget at most K each *)
Lemma wild_steps_uniform : forall U st d K, wild_steps U d st -> List.NoDup (steps_end d st) ->
  List.Forall (fun p => (length (fst p) <= K)%nat) st ->
  (length (wild_part U (steps_end d st)) <= length (wild_part U d) + length st * K)%nat.
Proof.
intros U st d K Hs Hn HF. pose proof (wild_steps_count U st d Hs Hn) as L1.
pose proof (steps_budget_le st K HF) as L2. lia.
Qed.
Lemma wild_room_steps : forall U set k st d, wild_room U set k d -> wild_steps U d st ->
  (wfresh set (steps_budget st) <= k)%nat ->
  wild_room U set (k - wfresh set (steps_budget st)) (steps_end d st).
Proof. intros U set k st d Hr Hs Hk. exact (wild_room_step U set k d _ _ Hr (wild_steps_incl U st d Hs) Hk). Qed.
(* THE RUN: from the empty start-up depot, after fewer than N stretches of budget at most K each (the driver's entry
   calls), there is room for one more such stretch when N * K <= u_wmax *)
Lemma wild_room_run : forall U st K N, wild_steps U [] st -> List.NoDup (steps_end [] st) ->
  List.Forall (fun p => (length (fst p) <= K)%nat) st -> (length st < N)%nat -> (N * K <= u_wmax U)%nat ->
  wild_room U [] K (steps_end [] st).
Proof.
intros U st K N Hs Hn HF HN HW. apply wild_room_of_count. cbn [length].
pose proof (wild_steps_uniform U st [] K Hs Hn HF) as L. rewrite wild_part_nil in L. cbn [length] in L.
assert (H1 : (S (length st) * K <= N * K)%nat) by (apply Nat.mul_le_mono_r; lia).
cbn [Nat.mul] in H1. lia.
Qed.

(* ============================================================================ *)
(* 4. THE JOURNAL                                                                *)
Section j. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
#[local] Abbreviation AJ := (ajournal_x (SK := SK) segs B PST ARx).
#[local] Abbreviation AJW := (ajournal_xw (SK := SK) segs B PST ARx).
#[local] Abbreviation AJR R := (ajournal_xR (SK := SK) segs B PST ARx R).
#[local] Abbreviation AJWR R := (ajournal_xwR (SK := SK) segs B PST ARx R).
(* the lemmas of this part over a world relation R (suffix R); each plain one below is its R form at wle *)
Lemma ajournal_xw_wild_countR : forall (R : world segs -> world segs -> Prop),
  forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS,
  AJWR R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS -> List.NoDup (st_depot S') ->
  (length (wild_part (as_universe B) (st_depot S')) <= length (wild_part (as_universe B) (st_depot S)) + length WS)%nat.
Proof.
intros R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS HJ Hn. exact (wild_count _ _ _ _ Hn (ajxR_wild HJ)).
Qed.
Lemma ajournal_xw_wild_count_setR : forall (R : world segs -> world segs -> Prop),
  forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS set,
  AJWR R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS -> List.NoDup (st_depot S') ->
  (length (wild_part (as_universe B) (st_depot S')) <=
   length (wild_part (as_universe B) (st_depot S)) + length set + wfresh set WS)%nat.
Proof.
intros R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS set HJ Hn.
exact (wild_count_set _ _ _ set _ Hn (ajxR_wild HJ)).
Qed.
Lemma ajournal_xw_roomR : forall (R : world segs -> world segs -> Prop),
  forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS set kr,
  AJWR R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS ->
  wild_room (as_universe B) set kr (st_depot S) -> (wfresh set WS <= kr)%nat ->
  wild_room (as_universe B) set (kr - wfresh set WS) (st_depot S').
Proof.
intros R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS set kr HJ Hr Hk.
exact (wild_room_step _ _ _ _ _ _ Hr (ajxR_wild HJ) Hk).
Qed.
Lemma ajournal_xw_admitsR : forall (R : world segs -> world segs -> Prop),
  forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k WS set kr tr,
  AJWR R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k WS -> List.NoDup (st_depot Sc) ->
  wild_room (as_universe B) set kr (st_depot S) -> (wfresh set WS <= kr)%nat ->
  inU (as_universe B) tr -> In tr set \/ (wfresh set WS < kr)%nat ->
  admits (as_universe B) tr Sc.
Proof.
intros R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k WS set kr tr HJ Hn Hr Hk Htr Hc.
apply (wild_room_admits _ set (kr - wfresh set WS) Sc tr Hn); [exact (wild_room_step _ _ _ _ _ _ Hr (ajxR_wild HJ) Hk) | exact Htr |].
destruct Hc as [H|H]; [left; exact H | right; lia].
Qed.
Lemma ajournal_xw_normR : forall (R : world segs -> world segs -> Prop),
  forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS0 ws set,
  AJWR R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k (WS0 ++ ws) ->
  AJWR R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k (WS0 ++ (set ++ wild_fresh set ws)).
Proof.
intros R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS0 ws set HJ.
apply (ajx_budgetR _ HJ). eapply wild_incl_mono; [|exact (ajxR_wild HJ)].
apply incl_app; [apply incl_appl, incl_refl | apply incl_appr, wild_fresh_cover].
Qed.
Lemma ajournal_xw_rebaseR : forall (R : world segs -> world segs -> Prop),
  forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS,
  AJWR R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS ->
  AJR R STK sp0 FP ly (set_depot (st_depot S') S) Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof.
intros R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS HJ.
unfold ajournal_xR, ajournal_xwR. apply ajxR_intro.
- exact (ajxR_ar HJ).
- exact (ajxR_ly HJ).
- exact (ajxR_secs HJ).
- exact (ajxR_rel HJ).
- exact (ajxR_io HJ).
- exact (ajxR_frs HJ).
- exact (ajxR_nev HJ).
- exact (ajxR_k HJ).
- exact (ajxR_hi HJ).
- exact (ajxR_blk HJ).
- exact (ajxR_img HJ).
- exact (ajxR_frm HJ).
- exact (ajxR_gone HJ).
- exact (ajxR_pres HJ).
- exact (ajxR_stk HJ).
- exact (ajxR_extra HJ).
- exact (ajxR_qt HJ).
- exact (wild_part_same (as_universe B) (st_depot S') []).
Qed.
Lemma ajournal_xw_unbaseR : forall (R : world segs -> world segs -> Prop),
  forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k d WS0 WS1,
  AJWR R STK sp0 FP ly (set_depot d S) Hp W mem md own ly' S' Hp' W' mem' md' k WS1 ->
  incl (wild_part (as_universe B) d) (wild_part (as_universe B) (st_depot S) ++ WS0) ->
  AJWR R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k (WS0 ++ WS1).
Proof.
intros R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k d WS0 WS1 HJ Hd.
unfold ajournal_xwR. apply ajxR_intro.
- exact (ajxR_ar HJ).
- exact (ajxR_ly HJ).
- exact (ajxR_secs HJ).
- exact (ajxR_rel HJ).
- exact (ajxR_io HJ).
- exact (ajxR_frs HJ).
- exact (ajxR_nev HJ).
- exact (ajxR_k HJ).
- exact (ajxR_hi HJ).
- exact (ajxR_blk HJ).
- exact (ajxR_img HJ).
- exact (ajxR_frm HJ).
- exact (ajxR_gone HJ).
- exact (ajxR_pres HJ).
- exact (ajxR_stk HJ).
- exact (ajxR_extra HJ).
- exact (ajxR_qt HJ).
- exact (wild_incl_trans _ _ _ _ _ (ajxR_wild HJ) Hd).
Qed.
Lemma ajournal_xw_unbase0R : forall (R : world segs -> world segs -> Prop),
  forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k d WS0,
  AJR R STK sp0 FP ly (set_depot d S) Hp W mem md own ly' S' Hp' W' mem' md' k ->
  incl (wild_part (as_universe B) d) (wild_part (as_universe B) (st_depot S) ++ WS0) ->
  AJWR R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS0.
Proof.
intros R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k d WS0 HJ Hd.
rewrite <- (app_nil_r WS0). exact (ajournal_xw_unbaseR R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k d WS0 [] HJ Hd).
Qed.
Lemma afn_pre_x_at_wR : forall (R : world segs -> world segs -> Prop),
  forall STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k WS regsc STK1 (o : Z) ch1,
  AJWR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k WS ->
  spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  YK0s.ret_ok (getr regsc 1) -> 4096 <= raZ regsc ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  achain lyc (aview segs (w_H W) memc) (spZ regsc) (s0Z regsc) ch1 ->
  afn_pre_x segs B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1.
Proof.
intros R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k WS regsc STK1 o ch1 HJ.
exact (afn_pre_x_atR segs B PST ARx R STK sp0 FP ly _ Hp W0 mem md own lyc Sc Hpc W memc mdc k regsc STK1 o ch1
  (ajournal_xw_rebaseR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k WS HJ)).
Qed.


(* THE COUNT OF A JOURNAL (a Theorem Labs lane 22:03Z item 5) *)
Lemma ajournal_xw_wild_count : forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS,
  AJW STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS -> List.NoDup (st_depot S') ->
  (length (wild_part (as_universe B) (st_depot S')) <= length (wild_part (as_universe B) (st_depot S)) + length WS)%nat.
Proof. exact (ajournal_xw_wild_countR (@wle segs)). Qed.
Lemma ajournal_xw_wild_count_set : forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS set,
  AJW STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS -> List.NoDup (st_depot S') ->
  (length (wild_part (as_universe B) (st_depot S')) <=
   length (wild_part (as_universe B) (st_depot S)) + length set + wfresh set WS)%nat.
Proof. exact (ajournal_xw_wild_count_setR (@wle segs)). Qed.
(* the entry room across the journal so far *)
Lemma ajournal_xw_room : forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS set kr,
  AJW STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS ->
  wild_room (as_universe B) set kr (st_depot S) -> (wfresh set WS <= kr)%nat ->
  wild_room (as_universe B) set (kr - wfresh set WS) (st_depot S').
Proof. exact (ajournal_xw_roomR (@wle segs)). Qed.
(* THE WALK'S ADMISSION of an allocator call at the current state Sc: from the room the text states at its entry S
   and its journal so far (budget WS), for a trace in the set, or with a fresh slot still unused *)
Lemma ajournal_xw_admits : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k WS set kr tr,
  AJW STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k WS -> List.NoDup (st_depot Sc) ->
  wild_room (as_universe B) set kr (st_depot S) -> (wfresh set WS <= kr)%nat ->
  inU (as_universe B) tr -> In tr set \/ (wfresh set WS < kr)%nat ->
  admits (as_universe B) tr Sc.
Proof. exact (ajournal_xw_admitsR (@wle segs)). Qed.
(* a budget replaced by its known set and its fresh part (repeats of a known trace dropped) *)
Lemma ajournal_xw_norm : forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS0 ws set,
  AJW STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k (WS0 ++ ws) ->
  AJW STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k (WS0 ++ (set ++ wild_fresh set ws)).
Proof. exact (ajournal_xw_normR (@wle segs)). Qed.

(* THE REBASE: a journal at budget WS from S is one at the empty budget from S with its depot moved to the current
   one; no other conjunct reads the entry depot (they read st_secs, frames = st_fs, ablocks = st_chunks, st_nev) *)
Lemma ajournal_xw_rebase : forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS,
  AJW STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS ->
  AJ STK sp0 FP ly (set_depot (st_depot S') S) Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof. exact (ajournal_xw_rebaseR (@wle segs)). Qed.
(* ... and back: a journal from the moved entry, with the moved depot's wild part covered from S *)
Lemma ajournal_xw_unbase : forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k d WS0 WS1,
  AJW STK sp0 FP ly (set_depot d S) Hp W mem md own ly' S' Hp' W' mem' md' k WS1 ->
  incl (wild_part (as_universe B) d) (wild_part (as_universe B) (st_depot S) ++ WS0) ->
  AJW STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k (WS0 ++ WS1).
Proof. exact (ajournal_xw_unbaseR (@wle segs)). Qed.
(* the step back after an empty-budget rule: the caller's journal at its own budget WS0 again *)
Lemma ajournal_xw_unbase0 : forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k d WS0,
  AJ STK sp0 FP ly (set_depot d S) Hp W mem md own ly' S' Hp' W' mem' md' k ->
  incl (wild_part (as_universe B) d) (wild_part (as_universe B) (st_depot S) ++ WS0) ->
  AJW STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS0.
Proof. exact (ajournal_xw_unbase0R (@wle segs)). Qed.
(* YCbqG.v's afn_pre_x_at at any caller budget *)
Lemma afn_pre_x_at_w : forall STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k WS regsc STK1 (o : Z) ch1,
  AJW STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k WS ->
  spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  YK0s.ret_ok (getr regsc 1) -> 4096 <= raZ regsc ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  achain lyc (aview segs (w_H W) memc) (spZ regsc) (s0Z regsc) ch1 ->
  afn_pre_x segs B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1.
Proof. exact (afn_pre_x_at_wR (@wle segs)). Qed.

(* ============================================================================ *)
(* 5. BUDGETED POSTS: the old posts with the journal at a budget WS the post chooses, of which the text states P WS *)
Definition apost_base_xb (P : list (list Z) -> Prop) (STK : Z) (FP : list (Z * Z)) (regs : bvmap 5 word) ly S
  (Hp : list Z) (W : world segs) mem md
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' Hp' regs' mem' md' k WS,
    c' = mkCfg (YK11.mkst regs' (YK11.getr regs 1) mem' (YK11.seg_rom segs)) md' /\
    P WS /\ AJW STK (spZ regs) FP ly S Hp W mem md [] ly' S' Hp' W' mem' md' k WS /\
    aregs_preserved regs regs' /\ Q ly' S' Hp' W' regs' mem' md'.
Definition apost_base_xbF (P : list (list Z) -> Prop) (STK : Z) (FP : list (Z * Z)) (regs : bvmap 5 word) ly S
  (Hp : list Z) (W : world segs) mem md
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' Hp' regs' mem' md' k WS,
    c' = mkCfg (@YK11.mkst fx' regs' (YK11.getr regs 1) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\
    P WS /\ AJW STK (spZ regs) FP ly S Hp W mem md [] ly' S' Hp' W' mem' md' k WS /\
    aregs_preserved regs regs' /\ Q ly' S' Hp' W' regs' mem' md'.
Definition fpostW_xb (P : list (list Z) -> Prop) (STK d : Z) (FP : list (Z * Z)) (regs : bvmap 5 word) ly S
  (Hp : list Z) (W : world segs) mem md
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' Hp' regs' mem' md' k WS,
    c' = mkCfg (YK11.mkst regs' (YK11.getr regs 1) mem' (YK11.seg_rom segs)) md' /\
    P WS /\ AJW (STK + d) (spZ regs + d) FP ly S Hp W mem md [] ly' S' Hp' W' mem' md' k WS /\
    (forall a, spZ regs <= a < spZ regs + d -> ~ inFP FP a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
    aregs_preserved regs regs' /\ Q ly' S' Hp' W' regs' mem' md'.
Definition fpostWF_xb (P : list (list Z) -> Prop) (STK d : Z) (FP : list (Z * Z)) (regs : bvmap 5 word) ly S
  (Hp : list Z) (W : world segs) mem md
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' Hp' regs' mem' md' k WS,
    c' = mkCfg (@YK11.mkst fx' regs' (YK11.getr regs 1) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\
    P WS /\ AJW (STK + d) (spZ regs + d) FP ly S Hp W mem md [] ly' S' Hp' W' mem' md' k WS /\
    (forall a, spZ regs <= a < spZ regs + d -> ~ inFP FP a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
    aregs_preserved regs regs' /\ Q ly' S' Hp' W' regs' mem' md'.
(* the four budgeted posts over a world relation R: COPIES of the bodies above with the journal at R (ajournal_xwR R).
   The plain bodies stay as they are, because proof lines in other files unfold them and read the body; the guard
   lemmas *_R_wle (by reflexivity) check that each plain post IS its R form at wle, so the copies cannot drift. *)
Definition apost_base_xbR (R : world segs -> world segs -> Prop) (P : list (list Z) -> Prop) (STK : Z)
  (FP : list (Z * Z)) (regs : bvmap 5 word) ly S (Hp : list Z) (W : world segs) mem md
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' Hp' regs' mem' md' k WS,
    c' = mkCfg (YK11.mkst regs' (YK11.getr regs 1) mem' (YK11.seg_rom segs)) md' /\
    P WS /\ ajournal_xwR (SK := SK) segs B PST ARx R STK (spZ regs) FP ly S Hp W mem md [] ly' S' Hp' W' mem' md' k WS /\
    aregs_preserved regs regs' /\ Q ly' S' Hp' W' regs' mem' md'.
Lemma apost_base_xb_R_wle : forall P STK FP regs ly S Hp W mem md Q,
  apost_base_xb P STK FP regs ly S Hp W mem md Q = apost_base_xbR (@wle segs) P STK FP regs ly S Hp W mem md Q.
Proof. reflexivity. Qed.
Definition apost_base_xbFR (R : world segs -> world segs -> Prop) (P : list (list Z) -> Prop) (STK : Z)
  (FP : list (Z * Z)) (regs : bvmap 5 word) ly S (Hp : list Z) (W : world segs) mem md
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' Hp' regs' mem' md' k WS,
    c' = mkCfg (@YK11.mkst fx' regs' (YK11.getr regs 1) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\
    P WS /\ ajournal_xwR (SK := SK) segs B PST ARx R STK (spZ regs) FP ly S Hp W mem md [] ly' S' Hp' W' mem' md' k WS /\
    aregs_preserved regs regs' /\ Q ly' S' Hp' W' regs' mem' md'.
Lemma apost_base_xbF_R_wle : forall P STK FP regs ly S Hp W mem md Q,
  apost_base_xbF P STK FP regs ly S Hp W mem md Q = apost_base_xbFR (@wle segs) P STK FP regs ly S Hp W mem md Q.
Proof. reflexivity. Qed.
Definition fpostW_xbR (R : world segs -> world segs -> Prop) (P : list (list Z) -> Prop) (STK d : Z)
  (FP : list (Z * Z)) (regs : bvmap 5 word) ly S (Hp : list Z) (W : world segs) mem md
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' Hp' regs' mem' md' k WS,
    c' = mkCfg (YK11.mkst regs' (YK11.getr regs 1) mem' (YK11.seg_rom segs)) md' /\
    P WS /\ ajournal_xwR (SK := SK) segs B PST ARx R (STK + d) (spZ regs + d) FP ly S Hp W mem md [] ly' S' Hp' W' mem' md' k WS /\
    (forall a, spZ regs <= a < spZ regs + d -> ~ inFP FP a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
    aregs_preserved regs regs' /\ Q ly' S' Hp' W' regs' mem' md'.
Lemma fpostW_xb_R_wle : forall P STK d FP regs ly S Hp W mem md Q,
  fpostW_xb P STK d FP regs ly S Hp W mem md Q = fpostW_xbR (@wle segs) P STK d FP regs ly S Hp W mem md Q.
Proof. reflexivity. Qed.
(* a budgeted callee text that concludes fpostW_xb (its journal at wle) concludes the R form at every R that contains
   wle (YCbqG.v ajournal_xwR_mono on the journal conjunct; the fpostW_xb twin of YCbqGcallW.v fpostW_x_R_lift) *)
Lemma fpostW_xb_R_lift : forall (R : world segs -> world segs -> Prop), (forall W W', wle W W' -> R W W') ->
  forall P STK d FP regs ly S Hp W mem md Q W' c',
  fpostW_xb P STK d FP regs ly S Hp W mem md Q W' c' -> fpostW_xbR R P STK d FP regs ly S Hp W mem md Q W' c'.
Proof.
intros R Hsub P STK d FP regs ly S Hp W mem md Q W' c'
  (ly' & S' & Hp' & regs' & mem' & md' & k & WS & Hc & HP & HJ & HX & Hpr & HQ).
exists ly', S', Hp', regs', mem', md', k, WS. split; [exact Hc|]. split; [exact HP|].
split; [exact (ajournal_xwR_mono (SK := SK) segs B PST ARx (@wle segs) R Hsub (STK + d) (spZ regs + d) FP ly S Hp W
                 mem md [] ly' S' Hp' W' mem' md' k WS HJ)
       | split; [exact HX | split; [exact Hpr | exact HQ]]].
Qed.
Definition fpostWF_xbR (R : world segs -> world segs -> Prop) (P : list (list Z) -> Prop) (STK d : Z)
  (FP : list (Z * Z)) (regs : bvmap 5 word) ly S (Hp : list Z) (W : world segs) mem md
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' Hp' regs' mem' md' k WS,
    c' = mkCfg (@YK11.mkst fx' regs' (YK11.getr regs 1) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\
    P WS /\ ajournal_xwR (SK := SK) segs B PST ARx R (STK + d) (spZ regs + d) FP ly S Hp W mem md [] ly' S' Hp' W' mem' md' k WS /\
    (forall a, spZ regs <= a < spZ regs + d -> ~ inFP FP a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
    aregs_preserved regs regs' /\ Q ly' S' Hp' W' regs' mem' md'.
Lemma fpostWF_xb_R_wle : forall P STK d FP regs ly S Hp W mem md Q,
  fpostWF_xb P STK d FP regs ly S Hp W mem md Q = fpostWF_xbR (@wle segs) P STK d FP regs ly S Hp W mem md Q.
Proof. reflexivity. Qed.

(* the four closers below over a world relation R *)
Lemma apost_base_xb_of_xR : forall (R : world segs -> world segs -> Prop),
  forall (P : list (list Z) -> Prop) STK FP regs ly S Hp W mem md Q W' c', P [] ->
  apost_base_xR (SK := SK) segs B PST ARx R STK FP regs ly S Hp W mem md Q W' c' ->
  apost_base_xbR R P STK FP regs ly S Hp W mem md Q W' c'.
Proof.
intros R P STK FP regs ly S Hp W mem md Q W' c' HP (ly' & S' & Hp' & regs' & mem' & md' & k & Hc & HJ & Hpr & HQ).
exists ly', S', Hp', regs', mem', md', k, []. split; [exact Hc|]. split; [exact HP|]. split; [exact HJ|].
split; [exact Hpr | exact HQ].
Qed.
Lemma apost_base_xbF_of_xR : forall (R : world segs -> world segs -> Prop),
  forall (P : list (list Z) -> Prop) STK FP regs ly S Hp W mem md Q W' c', P [] ->
  apost_base_xFR (SK := SK) segs B PST ARx R STK FP regs ly S Hp W mem md Q W' c' ->
  apost_base_xbFR R P STK FP regs ly S Hp W mem md Q W' c'.
Proof.
intros R P STK FP regs ly S Hp W mem md Q W' c' HP
  (fx' & ly' & S' & Hp' & regs' & mem' & md' & k & Hc & Hz & Hkf & HJ & Hpr & HQ).
exists fx', ly', S', Hp', regs', mem', md', k, []. split; [exact Hc|]. split; [exact Hz|]. split; [exact Hkf|].
split; [exact HP|]. split; [exact HJ|]. split; [exact Hpr | exact HQ].
Qed.
Lemma fpostW_xb_of_xR : forall (R : world segs -> world segs -> Prop),
  forall (P : list (list Z) -> Prop) STK d FP regs ly S Hp W mem md Q W' c', P [] ->
  fpostW_xR (SK := SK) segs B PST ARx R STK d FP regs ly S Hp W mem md Q W' c' ->
  fpostW_xbR R P STK d FP regs ly S Hp W mem md Q W' c'.
Proof.
intros R P STK d FP regs ly S Hp W mem md Q W' c' HP (ly' & S' & Hp' & regs' & mem' & md' & k & Hc & HJ & HX & Hpr & HQ).
exists ly', S', Hp', regs', mem', md', k, []. split; [exact Hc|]. split; [exact HP|]. split; [exact HJ|].
split; [exact HX|]. split; [exact Hpr | exact HQ].
Qed.
Lemma fpostWF_xb_of_xR : forall (R : world segs -> world segs -> Prop),
  forall (P : list (list Z) -> Prop) STK d FP regs ly S Hp W mem md Q W' c', P [] ->
  fpostWF_xR (SK := SK) segs B PST ARx R STK d FP regs ly S Hp W mem md Q W' c' ->
  fpostWF_xbR R P STK d FP regs ly S Hp W mem md Q W' c'.
Proof.
intros R P STK d FP regs ly S Hp W mem md Q W' c' HP
  (fx' & ly' & S' & Hp' & regs' & mem' & md' & k & Hc & Hz & Hkf & HJ & HX & Hpr & HQ).
exists fx', ly', S', Hp', regs', mem', md', k, []. split; [exact Hc|]. split; [exact Hz|]. split; [exact Hkf|].
split; [exact HP|]. split; [exact HJ|]. split; [exact HX|]. split; [exact Hpr | exact HQ].
Qed.

(* an old post is the budgeted one at every P that admits the empty budget (a callee with no wild site) *)
Lemma apost_base_xb_of_x : forall (P : list (list Z) -> Prop) STK FP regs ly S Hp W mem md Q W' c', P [] ->
  apost_base_x (SK := SK) segs B PST ARx STK FP regs ly S Hp W mem md Q W' c' ->
  apost_base_xb P STK FP regs ly S Hp W mem md Q W' c'.
Proof. exact (apost_base_xb_of_xR (@wle segs)). Qed.
Lemma apost_base_xbF_of_x : forall (P : list (list Z) -> Prop) STK FP regs ly S Hp W mem md Q W' c', P [] ->
  apost_base_xF (SK := SK) segs B PST ARx STK FP regs ly S Hp W mem md Q W' c' ->
  apost_base_xbF P STK FP regs ly S Hp W mem md Q W' c'.
Proof. exact (apost_base_xbF_of_xR (@wle segs)). Qed.
Lemma fpostW_xb_of_x : forall (P : list (list Z) -> Prop) STK d FP regs ly S Hp W mem md Q W' c', P [] ->
  fpostW_x (SK := SK) segs B PST ARx STK d FP regs ly S Hp W mem md Q W' c' ->
  fpostW_xb P STK d FP regs ly S Hp W mem md Q W' c'.
Proof. exact (fpostW_xb_of_xR (@wle segs)). Qed.
Lemma fpostWF_xb_of_x : forall (P : list (list Z) -> Prop) STK d FP regs ly S Hp W mem md Q W' c', P [] ->
  fpostWF_x (SK := SK) segs B PST ARx STK d FP regs ly S Hp W mem md Q W' c' ->
  fpostWF_xb P STK d FP regs ly S Hp W mem md Q W' c'.
Proof. exact (fpostWF_xb_of_xR (@wle segs)). Qed.

(* fpostW_xb_of_kept / fpostWF_xb_of_kept below over a world relation R *)
Lemma fpostW_xb_of_keptR : forall (R : world segs -> world segs -> Prop),
  forall (P : list (list Z) -> Prop) STK e FP regs ly S Hp W mem md
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  OR FPs ly2 S2 Hp2 W2 regs2 mem2 md2 k WS,
  0 <= STK -> P WS ->
  AJWR R (STK + e) (spZ regs + e) FP ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k WS ->
  cj_keptR (SK := SK) segs B PST R STK (spZ regs) OR FPs ly S W mem md ly2 S2 W2 mem2 md2 ->
  (forall a, inFP OR a -> inFP FP a) ->
  aregs_preserved regs regs2 -> Q ly2 S2 Hp2 W2 regs2 mem2 md2 ->
  fpostW_xbR R P STK e FP regs ly S Hp W mem md Q W2
    (mkCfg (YK11.mkst regs2 (YK11.getr regs 1) mem2 (YK11.seg_rom segs)) md2).
Proof.
intros R P STK e FP regs ly S Hp W mem md Q OR FPs ly2 S2 Hp2 W2 regs2 mem2 md2 k WS HSTK HPW HJ HK HOR HP HQ.
pose proof (ajxR_stk HJ) as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HK as (_ & _ & _ & _ & _ & K1 & _).
exists ly2, S2, Hp2, regs2, mem2, md2, k, WS. split; [reflexivity|]. split; [exact HPW|]. split; [exact HJ|].
split; [|split; [exact HP | exact HQ]].
intros a Ha Hf. apply K1; [zlia | zlia | intros Ho; exact (Hf (HOR a Ho))].
Qed.
Lemma fpostWF_xb_of_keptR : forall (R : world segs -> world segs -> Prop),
  forall (P : list (list Z) -> Prop) STK e FP regs ly S Hp W mem md
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  OR FPs ly2 S2 Hp2 W2 regs2 mem2 md2 k WS (fx' : YK11.FPState),
  frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fx fx' -> 0 <= STK -> P WS ->
  AJWR R (STK + e) (spZ regs + e) FP ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k WS ->
  cj_keptR (SK := SK) segs B PST R STK (spZ regs) OR FPs ly S W mem md ly2 S2 W2 mem2 md2 ->
  (forall a, inFP OR a -> inFP FP a) ->
  aregs_preserved regs regs2 -> Q ly2 S2 Hp2 W2 regs2 mem2 md2 ->
  fpostWF_xbR R P STK e FP regs ly S Hp W mem md Q W2
    (mkCfg (@YK11.mkst fx' regs2 (YK11.getr regs 1) mem2 (YK11.seg_rom segs)) md2).
Proof.
intros R P STK e FP regs ly S Hp W mem md Q OR FPs ly2 S2 Hp2 W2 regs2 mem2 md2 k WS fx' Hz Hkf HSTK HPW HJ HK HOR HP HQ.
pose proof (ajxR_stk HJ) as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HK as (_ & _ & _ & _ & _ & K1 & _).
exists fx', ly2, S2, Hp2, regs2, mem2, md2, k, WS. split; [reflexivity|]. split; [exact Hz|]. split; [exact Hkf|].
split; [exact HPW|]. split; [exact HJ|]. split; [|split; [exact HP | exact HQ]].
intros a Ha Hf. apply K1; [zlia | zlia | intros Ho; exact (Hf (HOR a Ho))].
Qed.

(* END of a budgeted caller-window walk: YCbqGcallW.v's fpostW_x_of_kept / fpostWF_x_of_kept at the walk's budget *)
Lemma fpostW_xb_of_kept : forall (P : list (list Z) -> Prop) STK e FP regs ly S Hp W mem md
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  OR FPs ly2 S2 Hp2 W2 regs2 mem2 md2 k WS,
  0 <= STK -> P WS ->
  AJW (STK + e) (spZ regs + e) FP ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k WS ->
  cj_kept (SK := SK) segs B PST STK (spZ regs) OR FPs ly S W mem md ly2 S2 W2 mem2 md2 ->
  (forall a, inFP OR a -> inFP FP a) ->
  aregs_preserved regs regs2 -> Q ly2 S2 Hp2 W2 regs2 mem2 md2 ->
  fpostW_xb P STK e FP regs ly S Hp W mem md Q W2
    (mkCfg (YK11.mkst regs2 (YK11.getr regs 1) mem2 (YK11.seg_rom segs)) md2).
Proof. exact (fpostW_xb_of_keptR (@wle segs)). Qed.
Lemma fpostWF_xb_of_kept : forall (P : list (list Z) -> Prop) STK e FP regs ly S Hp W mem md
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  OR FPs ly2 S2 Hp2 W2 regs2 mem2 md2 k WS (fx' : YK11.FPState),
  frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fx fx' -> 0 <= STK -> P WS ->
  AJW (STK + e) (spZ regs + e) FP ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k WS ->
  cj_kept (SK := SK) segs B PST STK (spZ regs) OR FPs ly S W mem md ly2 S2 W2 mem2 md2 ->
  (forall a, inFP OR a -> inFP FP a) ->
  aregs_preserved regs regs2 -> Q ly2 S2 Hp2 W2 regs2 mem2 md2 ->
  fpostWF_xb P STK e FP regs ly S Hp W mem md Q W2
    (mkCfg (@YK11.mkst fx' regs2 (YK11.getr regs 1) mem2 (YK11.seg_rom segs)) md2).
Proof. exact (fpostWF_xb_of_keptR (@wle segs)). Qed.

Section l.
Context {HL : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* THE ADMISSIONS WITH THE DEPOT PREMISE DISCHARGED: AR_laws_x's field 25 (alx_depot_nodup) gives List.NoDup of the
   depot at every ARx state; at a walk's current state that is the journal's ajx_ar *)
Lemma wild_room_admits_laws : forall U set k ly S Hp W mem md tr, ARx ly S Hp W mem md ->
  wild_room U set k (st_depot S) -> inU U tr -> In tr set \/ (0 < k)%nat -> admits U tr S.
Proof.
intros U set k ly S Hp W mem md tr HAR.
exact (wild_room_admits U set k S tr (alx_depot_nodup _ _ _ LAWS ly S Hp W mem md HAR)).
Qed.
Lemma ajournal_xw_admits_lawsR : forall (R : world segs -> world segs -> Prop),
  forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k WS set kr tr,
  AJWR R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k WS ->
  wild_room (as_universe B) set kr (st_depot S) -> (wfresh set WS <= kr)%nat ->
  inU (as_universe B) tr -> In tr set \/ (wfresh set WS < kr)%nat ->
  admits (as_universe B) tr Sc.
Proof.
intros R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k WS set kr tr HJ.
exact (ajournal_xw_admitsR R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k WS set kr tr HJ
  (alx_depot_nodup _ _ _ LAWS lyc Sc Hpc Wc memc mdc (ajxR_ar HJ))).
Qed.
Lemma ajournal_xw_admits_laws : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k WS set kr tr,
  AJW STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k WS ->
  wild_room (as_universe B) set kr (st_depot S) -> (wfresh set WS <= kr)%nat ->
  inU (as_universe B) tr -> In tr set \/ (wfresh set WS < kr)%nat ->
  admits (as_universe B) tr Sc.
Proof. exact (ajournal_xw_admits_lawsR (@wle segs)). Qed.

(* aj_call_xb_sp below over a world relation R: R and its two laws first; the journals, the callee's post
   apost_base_xbR and the conclusion at R *)
Lemma aj_call_xb_spR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
  (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
  forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0 STK1 FP1 (o : Z) raw ch1
  (P : list (list Z) -> Prop)
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  AJWR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS0 ->
  spZ (ms_regs ms) = sp0 + o ->
  o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   SRrG segs R W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
     (apost_base_xbR R P STK1 FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q)) ->
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  SRrG segs R W (mkCfg ms mdc)
   (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1 WS1,
    c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\ P WS1 /\
    AJWR R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) (WS0 ++ WS1) /\
    AJWR R STK1 (sp0 + o) FP1 lyc Sc Hpc W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 /\
    aregs_preserved (ms_regs ms) regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros R Rr Rt W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0 STK1 FP1 o raw ch1 P Q
  HS Hrv HJ Hsp' Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
rewrite (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv).
eapply (SRrG_mono segs R).
{ apply Hcallee. eapply (afn_pre_x_at_wR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS0
  (ms_regs ms) STK1 o ch1); try eassumption.
  - rewrite Hra. exact Hraw.
  - unfold raZ. rewrite Hra. exact Hra4.
  - rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HPW & HJ1 & HP & HQ).
exists ly2, S2, Hp2, regs2, mem2, md2, k1, WS1. rewrite Hra. split; [reflexivity|]. split; [exact HPW|].
rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HQ]]].
change own with ([] ++ own). eapply (ajournal_xw_subR segs B PST ARx LAWS segs_low R Rt); [exact HJ | exact HJ1 | zlia | zlia | exact HF].
Qed.

(* THE CALL OF A BUDGETED CALLEE (YCbqGcall.v aj_call_x_sp): the caller at any budget WS0, the callee's text concludes
   in apost_base_xb P; after the call the caller's journal is at WS0 ++ WS1 for a WS1 with P WS1. *)
Lemma aj_call_xb_sp : forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0 STK1 FP1 (o : Z) raw ch1
  (P : list (list Z) -> Prop)
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  AJW STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS0 ->
  spZ (ms_regs ms) = sp0 + o ->
  o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   SRr segs W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
     (apost_base_xb P STK1 FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q)) ->
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  SRr segs W (mkCfg ms mdc)
   (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1 WS1,
    c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\ P WS1 /\
    AJW STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) (WS0 ++ WS1) /\
    AJW STK1 (sp0 + o) FP1 lyc Sc Hpc W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 /\
    aregs_preserved (ms_regs ms) regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof. exact (aj_call_xb_spR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* aj_call_xbF_sp below over a world relation R *)
Lemma aj_call_xbF_spR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
  (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
  forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0 STK1 FP1 (o : Z) raw ch1
  (P : list (list Z) -> Prop)
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  AJWR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS0 ->
  spZ (ms_regs ms) = sp0 + o ->
  o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   SRrG segs R W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
     (apost_base_xbFR R P STK1 FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q)) ->
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  SRrG segs R W (mkCfg ms mdc)
   (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1 WS1,
    c2 = mkCfg (@YK11.mkst fx' regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
    frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\ P WS1 /\
    AJWR R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) (WS0 ++ WS1) /\
    AJWR R STK1 (sp0 + o) FP1 lyc Sc Hpc W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 /\
    aregs_preserved (ms_regs ms) regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros R Rr Rt W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0 STK1 FP1 o raw ch1 P Q
  HS Hrv HJ Hsp' Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
rewrite (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv).
eapply (SRrG_mono segs R).
{ apply Hcallee. eapply (afn_pre_x_at_wR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS0
  (ms_regs ms) STK1 o ch1); try eassumption.
  - rewrite Hra. exact Hraw.
  - unfold raZ. rewrite Hra. exact Hra4.
  - rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HFZ & HFK & HPW & HJ1 & HP & HQ).
exists fx', ly2, S2, Hp2, regs2, mem2, md2, k1, WS1. rewrite Hra. split; [reflexivity|].
split; [exact HFZ|]. split; [exact HFK|]. split; [exact HPW|]. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HQ]]].
change own with ([] ++ own). eapply (ajournal_xw_subR segs B PST ARx LAWS segs_low R Rt); [exact HJ | exact HJ1 | zlia | zlia | exact HF].
Qed.
(* the float twin (YCbqGcall.v aj_call_xF_sp): the callee's text concludes in apost_base_xbF *)
Lemma aj_call_xbF_sp : forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0 STK1 FP1 (o : Z) raw ch1
  (P : list (list Z) -> Prop)
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  AJW STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS0 ->
  spZ (ms_regs ms) = sp0 + o ->
  o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   SRr segs W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
     (apost_base_xbF P STK1 FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q)) ->
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  SRr segs W (mkCfg ms mdc)
   (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1 WS1,
    c2 = mkCfg (@YK11.mkst fx' regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
    frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\ P WS1 /\
    AJW STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) (WS0 ++ WS1) /\
    AJW STK1 (sp0 + o) FP1 lyc Sc Hpc W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 /\
    aregs_preserved (ms_regs ms) regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof. exact (aj_call_xbF_spR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* aj_call_xbF below over a world relation R *)
Lemma aj_call_xbFR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
  (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
  forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0 STK1 FP1 (o : Z) spw raw ch1
  (P : list (list Z) -> Prop)
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  AJWR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS0 ->
  getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
  o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   SRrG segs R W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
     (apost_base_xbFR R P STK1 FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q)) ->
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  SRrG segs R W (mkCfg ms mdc)
   (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1 WS1,
    c2 = mkCfg (@YK11.mkst fx' regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
    frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\ P WS1 /\
    AJWR R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) (WS0 ++ WS1) /\
    AJWR R STK1 (sp0 + o) FP1 lyc Sc Hpc W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 /\
    aregs_preserved (ms_regs ms) regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros R Rr Rt W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0 STK1 FP1 o spw raw ch1 P Q
  HS Hrv HJ Hsp HE2 Hspw Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof (ajxR_stk HJ) as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _). assert (ASTACK = 16384) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. rewrite denot_SOff, HE2, Hspw. apply zcanon_small. zlia. }
exact (aj_call_xbF_spR R Rr Rt W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0 STK1 FP1 o raw ch1 P Q
  HS Hrv HJ Hsp' Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF).
Qed.
Lemma aj_call_xbF : forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0 STK1 FP1 (o : Z) spw raw ch1
  (P : list (list Z) -> Prop)
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  AJW STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS0 ->
  getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
  o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   SRr segs W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
     (apost_base_xbF P STK1 FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q)) ->
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  SRr segs W (mkCfg ms mdc)
   (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1 WS1,
    c2 = mkCfg (@YK11.mkst fx' regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
    frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\ P WS1 /\
    AJW STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) (WS0 ++ WS1) /\
    AJW STK1 (sp0 + o) FP1 lyc Sc Hpc W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 /\
    aregs_preserved (ms_regs ms) regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof. exact (aj_call_xbFR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.

(* aj_call_xWb below over a world relation R *)
Lemma aj_call_xWbR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
  (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
  forall W (regsc : bvmap 5 word) memc (pc : Z) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0
  STK1 e1 FP1 (o : Z) raw ch1 (P : list (list Z) -> Prop)
  (K : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  AJWR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k WS0 ->
  spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  0 <= e1 -> e1 mod 16 = 0 -> o + e1 <= 0 ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1 -> fwin_x segs lyc W regsc memc e1 ->
   SRrG segs R W (mkCfg (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom segs)) mdc)
     (fpostW_xbR R P STK1 e1 FP1 regsc lyc Sc Hpc W memc mdc K)) ->
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  SRrG segs R W (mkCfg (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom segs)) mdc)
    (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1 WS1,
       c2 = mkCfg (YK11.mkst regs2 raw mem2 (YK11.seg_rom segs)) md2 /\ P WS1 /\
       AJWR R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) (WS0 ++ WS1) /\
       AJWR R (STK1 + e1) (sp0 + o + e1) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 /\
       (forall a, sp0 + o <= a < sp0 + o + e1 -> ~ inFP FP1 a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
       aregs_preserved regsc regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros R Rr Rt W regsc memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0 STK1 e1 FP1 o raw ch1 P K
  HJ Hsp Hal Hneg Hstk1 Hbud He0 He16 Hetop Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_pres HJ) as Hpres.
pose proof (ajxR_stk HJ) as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & _).
assert (HPRE : afn_pre_x segs B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1).
{ eapply (afn_pre_x_at_wR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k WS0 regsc STK1 o ch1);
  try eassumption. - rewrite Hra. exact Hraw. - unfold raZ. rewrite Hra. exact Hra4. - rewrite Hsp. exact Hch. }
assert (HWIN : fwin_x segs lyc W regsc memc e1).
{ split; [exact He0|]. split; [exact He16|]. split; [rewrite Hsp, Etop; zlia|].
  intros a Ha. apply Hpres. rewrite Hsp in Ha. zlia. }
eapply (SRrG_mono segs R); [exact (Hcallee HPRE HWIN)|].
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HPW & HJ1 & HX & HP & HK).
exists ly2, S2, Hp2, regs2, mem2, md2, k1, WS1. split; [rewrite Hra; reflexivity|]. split; [exact HPW|].
rewrite Hsp in HJ1, HX.
split; [| split; [exact HJ1 | split; [exact HX | split; [exact HP | exact HK]]]].
change own with ([] ++ own). eapply (ajournal_xw_subR segs B PST ARx LAWS segs_low R Rt); [exact HJ | exact HJ1 | zlia | zlia | exact HF].
Qed.
(* THE CALL OF A BUDGETED CALLER-WINDOW CALLEE (YCbqGcallW.v aj_call_xW): the callee's text gives fpostW_xb P at its
   widened window (STK1 + e1) (sp + e1) *)
Lemma aj_call_xWb : forall W (regsc : bvmap 5 word) memc (pc : Z) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0
  STK1 e1 FP1 (o : Z) raw ch1 (P : list (list Z) -> Prop)
  (K : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  AJW STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k WS0 ->
  spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  0 <= e1 -> e1 mod 16 = 0 -> o + e1 <= 0 ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1 -> fwin_x segs lyc W regsc memc e1 ->
   SRr segs W (mkCfg (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom segs)) mdc)
     (fpostW_xb P STK1 e1 FP1 regsc lyc Sc Hpc W memc mdc K)) ->
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  SRr segs W (mkCfg (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom segs)) mdc)
    (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1 WS1,
       c2 = mkCfg (YK11.mkst regs2 raw mem2 (YK11.seg_rom segs)) md2 /\ P WS1 /\
       AJW STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) (WS0 ++ WS1) /\
       AJW (STK1 + e1) (sp0 + o + e1) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 /\
       (forall a, sp0 + o <= a < sp0 + o + e1 -> ~ inFP FP1 a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
       aregs_preserved regsc regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof. exact (aj_call_xWbR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* aj_call_xWb_sp below over a world relation R *)
Lemma aj_call_xWb_spR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
  (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
  forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0 STK1 e1 FP1 (o : Z) raw ch1
  (P : list (list Z) -> Prop)
  (K : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  AJWR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS0 ->
  spZ (ms_regs ms) = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  0 <= e1 -> e1 mod 16 = 0 -> o + e1 <= 0 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   fwin_x segs lyc W (ms_regs ms) (ms_mem ms) e1 ->
   SRrG segs R W (mkCfg (YK11.mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (YK11.seg_rom segs)) mdc)
     (fpostW_xbR R P STK1 e1 FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc K)) ->
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  SRrG segs R W (mkCfg ms mdc)
    (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1 WS1,
       c2 = mkCfg (YK11.mkst regs2 raw mem2 (YK11.seg_rom segs)) md2 /\ P WS1 /\
       AJWR R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) (WS0 ++ WS1) /\
       AJWR R (STK1 + e1) (sp0 + o + e1) FP1 lyc Sc Hpc W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 /\
       (forall a, sp0 + o <= a < sp0 + o + e1 -> ~ inFP FP1 a ->
          aview segs (w_H W2) mem2 a = aview segs (w_H W) (ms_mem ms) a) /\
       aregs_preserved (ms_regs ms) regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros R Rr Rt W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0 STK1 e1 FP1 o raw ch1 P K
  HS Hrv HJ Hsp Hal Hneg Hstk1 Hbud He0 He16 Hetop Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof (aj_call_xWbR R Rr Rt W (ms_regs ms) (ms_mem ms) (ss_pc ss) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0
  STK1 e1 FP1 o raw ch1 P K HJ Hsp Hal Hneg Hstk1 Hbud He0 He16 Hetop Hgp Htp Hra Hraw Hra4 Hch Hcallee HF) as G.
rewrite <- (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv) in G. exact G.
Qed.
Lemma aj_call_xWb_sp : forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0 STK1 e1 FP1 (o : Z) raw ch1
  (P : list (list Z) -> Prop)
  (K : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  AJW STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS0 ->
  spZ (ms_regs ms) = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  0 <= e1 -> e1 mod 16 = 0 -> o + e1 <= 0 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   fwin_x segs lyc W (ms_regs ms) (ms_mem ms) e1 ->
   SRr segs W (mkCfg (YK11.mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (YK11.seg_rom segs)) mdc)
     (fpostW_xb P STK1 e1 FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc K)) ->
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  SRr segs W (mkCfg ms mdc)
    (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1 WS1,
       c2 = mkCfg (YK11.mkst regs2 raw mem2 (YK11.seg_rom segs)) md2 /\ P WS1 /\
       AJW STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) (WS0 ++ WS1) /\
       AJW (STK1 + e1) (sp0 + o + e1) FP1 lyc Sc Hpc W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 /\
       (forall a, sp0 + o <= a < sp0 + o + e1 -> ~ inFP FP1 a ->
          aview segs (w_H W2) mem2 a = aview segs (w_H W) (ms_mem ms) a) /\
       aregs_preserved (ms_regs ms) regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof. exact (aj_call_xWb_spR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* aj_call_xWFb below over a world relation R *)
Lemma aj_call_xWFbR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
  (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
  forall W (regsc : bvmap 5 word) memc (pc : Z) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0
  STK1 e1 FP1 (o : Z) raw ch1 (P : list (list Z) -> Prop)
  (K : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  AJWR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k WS0 ->
  spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  0 <= e1 -> e1 mod 16 = 0 -> o + e1 <= 0 ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1 -> fwin_x segs lyc W regsc memc e1 ->
   SRrG segs R W (mkCfg (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom segs)) mdc)
     (fpostWF_xbR R P STK1 e1 FP1 regsc lyc Sc Hpc W memc mdc K)) ->
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  SRrG segs R W (mkCfg (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom segs)) mdc)
    (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1 WS1,
       c2 = mkCfg (@YK11.mkst fx' regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
       frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\ P WS1 /\
       AJWR R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) (WS0 ++ WS1) /\
       AJWR R (STK1 + e1) (sp0 + o + e1) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 /\
       (forall a, sp0 + o <= a < sp0 + o + e1 -> ~ inFP FP1 a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
       aregs_preserved regsc regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros R Rr Rt W regsc memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0 STK1 e1 FP1 o raw ch1 P K
  HJ Hsp Hal Hneg Hstk1 Hbud He0 He16 Hetop Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_pres HJ) as Hpres.
pose proof (ajxR_stk HJ) as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & _).
assert (HPRE : afn_pre_x segs B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1).
{ eapply (afn_pre_x_at_wR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k WS0 regsc STK1 o ch1);
  try eassumption. - rewrite Hra. exact Hraw. - unfold raZ. rewrite Hra. exact Hra4. - rewrite Hsp. exact Hch. }
assert (HWIN : fwin_x segs lyc W regsc memc e1).
{ split; [exact He0|]. split; [exact He16|]. split; [rewrite Hsp, Etop; zlia|].
  intros a Ha. apply Hpres. rewrite Hsp in Ha. zlia. }
eapply (SRrG_mono segs R); [exact (Hcallee HPRE HWIN)|].
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HFZ & HFK & HPW & HJ1 & HX & HP & HK).
exists fx', ly2, S2, Hp2, regs2, mem2, md2, k1, WS1. split; [rewrite Hra; reflexivity|].
split; [exact HFZ|]. split; [exact HFK|]. split; [exact HPW|]. rewrite Hsp in HJ1, HX.
split; [| split; [exact HJ1 | split; [exact HX | split; [exact HP | exact HK]]]].
change own with ([] ++ own). eapply (ajournal_xw_subR segs B PST ARx LAWS segs_low R Rt); [exact HJ | exact HJ1 | zlia | zlia | exact HF].
Qed.
(* the window AND float twin (YCbqGcallW.v aj_call_xWF): the callee's text gives fpostWF_xb P *)
Lemma aj_call_xWFb : forall W (regsc : bvmap 5 word) memc (pc : Z) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0
  STK1 e1 FP1 (o : Z) raw ch1 (P : list (list Z) -> Prop)
  (K : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  AJW STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k WS0 ->
  spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  0 <= e1 -> e1 mod 16 = 0 -> o + e1 <= 0 ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1 -> fwin_x segs lyc W regsc memc e1 ->
   SRr segs W (mkCfg (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom segs)) mdc)
     (fpostWF_xb P STK1 e1 FP1 regsc lyc Sc Hpc W memc mdc K)) ->
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  SRr segs W (mkCfg (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom segs)) mdc)
    (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1 WS1,
       c2 = mkCfg (@YK11.mkst fx' regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
       frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\ P WS1 /\
       AJW STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) (WS0 ++ WS1) /\
       AJW (STK1 + e1) (sp0 + o + e1) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 /\
       (forall a, sp0 + o <= a < sp0 + o + e1 -> ~ inFP FP1 a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
       aregs_preserved regsc regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof. exact (aj_call_xWFbR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* aj_call_xWFb_sp below over a world relation R *)
Lemma aj_call_xWFb_spR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
  (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
  forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0 STK1 e1 FP1 (o : Z) raw ch1
  (P : list (list Z) -> Prop)
  (K : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  AJWR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS0 ->
  spZ (ms_regs ms) = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  0 <= e1 -> e1 mod 16 = 0 -> o + e1 <= 0 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   fwin_x segs lyc W (ms_regs ms) (ms_mem ms) e1 ->
   SRrG segs R W (mkCfg (YK11.mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (YK11.seg_rom segs)) mdc)
     (fpostWF_xbR R P STK1 e1 FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc K)) ->
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  SRrG segs R W (mkCfg ms mdc)
    (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1 WS1,
       c2 = mkCfg (@YK11.mkst fx' regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
       frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\ P WS1 /\
       AJWR R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) (WS0 ++ WS1) /\
       AJWR R (STK1 + e1) (sp0 + o + e1) FP1 lyc Sc Hpc W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 /\
       (forall a, sp0 + o <= a < sp0 + o + e1 -> ~ inFP FP1 a ->
          aview segs (w_H W2) mem2 a = aview segs (w_H W) (ms_mem ms) a) /\
       aregs_preserved (ms_regs ms) regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros R Rr Rt W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0 STK1 e1 FP1 o raw ch1 P K
  HS Hrv HJ Hsp Hal Hneg Hstk1 Hbud He0 He16 Hetop Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof (aj_call_xWFbR R Rr Rt W (ms_regs ms) (ms_mem ms) (ss_pc ss) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0
  STK1 e1 FP1 o raw ch1 P K HJ Hsp Hal Hneg Hstk1 Hbud He0 He16 Hetop Hgp Htp Hra Hraw Hra4 Hch Hcallee HF) as G.
rewrite <- (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv) in G. exact G.
Qed.
Lemma aj_call_xWFb_sp : forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0 STK1 e1 FP1 (o : Z) raw ch1
  (P : list (list Z) -> Prop)
  (K : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  AJW STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS0 ->
  spZ (ms_regs ms) = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  0 <= e1 -> e1 mod 16 = 0 -> o + e1 <= 0 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   fwin_x segs lyc W (ms_regs ms) (ms_mem ms) e1 ->
   SRr segs W (mkCfg (YK11.mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (YK11.seg_rom segs)) mdc)
     (fpostWF_xb P STK1 e1 FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc K)) ->
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  SRr segs W (mkCfg ms mdc)
    (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1 WS1,
       c2 = mkCfg (@YK11.mkst fx' regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
       frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\ P WS1 /\
       AJW STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) (WS0 ++ WS1) /\
       AJW (STK1 + e1) (sp0 + o + e1) FP1 lyc Sc Hpc W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 /\
       (forall a, sp0 + o <= a < sp0 + o + e1 -> ~ inFP FP1 a ->
          aview segs (w_H W2) mem2 a = aview segs (w_H W) (ms_mem ms) a) /\
       aregs_preserved (ms_regs ms) regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof. exact (aj_call_xWFb_spR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
End l.
End j.
