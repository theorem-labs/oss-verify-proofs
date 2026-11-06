(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PRH_Refute.v, with its module paths and module names changed; 1 of its 248 lines of code is new or changed. *)
(* Theorem Labs, 2026-10 (#102, the K1-batch walk-kit lead's dead-arm sweep): THE REFUTATION FAMILY of the ENTRY-KEYED texts' refusal arms
   (the kit owner's order to the rtt102 walk: one mechanism; no rtt lane had started it, per the rtt102 walk, 2026-10-29). NOT A KIT
   TEXT: it Requires lib/A/PresetCfnA.v (P8 at the instance, preset_no_refusal), so it is built in the consumer tree
   and no kit text Requires it (nor does PRH_NamesCheck.v, which is in the kit's closure).
   WHAT IS REFUTED, AND WHERE. A REAL refusal is a NULL of the allocator on a path the engine realizes: amreal
   (lib/Reusable/YG0d.v:68-87) follows only grant answers, so every allocator result a walk holds comes with
   `apath t trc r /\ YG0d.gflag trc = true` (malloc_cf directly; a realloc's NULL as ReallocP.mt_refused, both steps
   granted). That pair is THE MACHINE-LEVEL REFUSAL OUTCOME (prh_granted_null below). At a CONSUMER allocation of the
   run (PRH_Base.prh_cons_from over PresetRun.hcons) and the run position iface_room_pos at the call's own state, it is
   impossible: a NULL on a granted path is primary-only (YGcfPath.malloc_cf_null_path, the fact behind
   YG0dcf.malloc_cf_null_post's from_primary), P8 at that position leaves only an environment refusal as its cause
   (PresetCfnA.preset_no_refusal under run_allocs_follow), and on a granted path the rpost flag is true
   (PRH_Base.prh_rpost_granted). prh_refute_follow is that, at the engine level; prh_refute_at / prh_refute_window are
   it at a position of the run (the shape `prh_cons_from .. -> iface_room_pos .. -> refusal -> False`), and the
   per-callee corollaries name each callee's own event list.
   WHY NOT FROM A CALLEE'S POST. A callee's TEXT-LEVEL refusal outcome (pj_write's failed arm, tx's REFUSED arm
   prhtx_refused_at, parse_noting's ran' = 1, pj_set's res = -1, pj_string's a = 0) cannot be refuted from the post
   alone: no post carries the granted path, and without it the refusal is consistent with every other fact a post
   states - an ENVIRONMENT refusal at a state with room (YGcfRoom.room_of_cf reads the blocks, the quarantine items and
   the batch count, not the class-exhausted flag that malloc_cf_null_post sets). And no walk can assume the run
   hypothesis inside its body (lib/Reusable/YA0n.v:35-38: SRr is a continuation over trace sets with no forall
   introduction), so the exclusion is made where the path is held, at the allocator call, and carried out of the call
   by the TEXT: an ENTRY-KEYED text takes prh_cons_from at entry and states the arm dead (tpj_string_specX
   DEAD-PJSTRING, tpj_set_specX DEAD-PJSET, tpj_write_specX DEAD-PJWRITE and its callees' DEAD-PUT /
   -INDENT / -PUTSTRING / -WRITEVALUE (prh_granted), the tx family's DEAD-TXPUT / -TXSTRING / -TXLINE / -TXVALUE
   (`f0 = 0 -> f1 = 0`, the window guarded by f0 = 0); the three check texts), and a POST-IMPLICATION text states the
   outcome clause in its post (parse_noting: ran' = 0 under prh_cons_from and its pick condition,
   PRH_FnCheck.tparse_noting_specX). A walk then refutes the callee's refusal outcome from the dead conjunct (tx's
   REFUSED arm has f1 = 1, its FAILED-AT-ENTRY arm f0 <> 0); prh_refute_pj_write_failed below is the one such step
   that needs the writer model (pj_write's failed arm, w_failed <> 0, from prh_granted and no chosen failure in the
   window). The walks of those texts close their dead conjuncts with the engine lemmas here (tx_put's raw realloc:
   prh_refute_tx_put) or with their callees' dead conjuncts and outcome clauses.
   Nothing here is a function's proof (rule 24). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG01 YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG00cf YG01cf YGcfPath.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ReallocP YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetRun PresetSite17.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomCounts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterApp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Base PRH_FnWriter PRH_FnPj PRH_FnTx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetCfnA.
(* stdpp, through the LPS modules, shadows several list names; the lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- the run side: the j-th event of a text's own list is the run's event at i + j ---- *)
Lemma prh_firstn_nth : forall (A : Type) (l : list A) n j (a : A),
  nth_error (firstn n l) j = Some a -> nth_error l j = Some a.
Proof.
  intros A l. induction l as [|b l IH]; intros n j a H.
  - destruct n; destruct j; cbn in H; discriminate H.
  - destruct n as [|n]; [destruct j; cbn in H; discriminate H|].
    destruct j as [|j]; cbn in H |- *; [exact H | exact (IH n j a H)].
Qed.

Lemma prh_skipn_nth : forall (A : Type) i (l : list A) j, nth_error (skipn i l) j = nth_error l (i + j).
Proof.
  intros A i. induction i as [|i IH]; intros l j; [reflexivity|].
  destruct l as [|b l]; cbn; [destruct j; reflexivity | apply IH].
Qed.

Lemma prh_run_at_nth : forall sm x os i E j e, PRH_Base.prh_run_at sm x os i E -> nth_error E j = Some e ->
  nth_error (PresetRun.hruns sm x os) (i + j) = Some e.
Proof.
  unfold PRH_Base.prh_run_at. intros sm x os i E j e H He. rewrite <- H in He.
  rewrite <- prh_skipn_nth. exact (prh_firstn_nth _ _ _ _ _ He).
Qed.

(* an allocation inside a consumer window is a consumer allocation (prh_cons_from unfolded at one event) *)
Lemma prh_cons_at : forall sm x os i k j e, PRH_Base.prh_cons_from sm x os i k -> (j < k)%nat ->
  nth_error (PresetRun.hruns sm x os) (i + j) = Some e -> PresetSite17.is_alloc e = true ->
  nth (i + j) (PresetRun.hcons sm x os) false = true.
Proof.
  unfold PRH_Base.prh_cons_from. intros sm x os i k j e Hc Hj He Ha. pose proof (Hc j e Hj He) as H.
  destruct e; try discriminate Ha; exact H.
Qed.

(* the engine's two granted-path flags are the same function (ReallocP keeps its own copy of YG0d.gflag) *)
Lemma prh_gflag_eq : forall trc, ReallocP.gflag trc = YG0d.gflag trc.
Proof. induction trc as [|[q z] trc IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Section rf. Context {ci : CfImg} {cp : CfParams}.

(* ---- THE MACHINE-LEVEL REFUSAL OUTCOME at a state s: the allocator returned NULL on a path the engine realizes -
   malloc_cf with every kernel answer granted (amreal's apath / gflag pair, the form amalloc_realizes_cf's walks
   hold), or a realloc's NULL witness ReallocP.mt_refused (its entry free_cf PNull and its inner malloc_cf, both on
   granted paths; the form the realloc rules' NULL arm gives, YGcallRx / YGcallRcf.realloc_x_null_post_cf) ---- *)
Definition prh_granted_null (s : astate) : Prop :=
  (exists n tr trc s', YG00.apath (YG00cf.malloc_cf n tr s) trc (PNull, s') /\ YG0d.gflag trc = true) \/
  (exists n tr s', ReallocP.mt_refused YG00cf.malloc_cf YG00cf.free_cf n tr s s').

(* ---- THE ENGINE LEVEL, under the walk's fact run_allocs_follow (PresetCfnA: one malloc_cf made at a consumer
   allocation of the run with P8's premises in its state) ---- *)
Lemma prh_refute_malloc_follow : forall U sm x H0 s n tr trc s',
  Wf_cf U s -> Z.of_nat (length x) <= PresetReqAt.MAXB -> PresetCfnA.run_allocs_follow sm x H0 s ->
  YG00.apath (YG00cf.malloc_cf n tr s) trc (PNull, s') -> YG0d.gflag trc = true -> False.
Proof.
  intros U sm x H0 s n tr trc s' W Hx RAF Hp Hg.
  pose proof W as W0. unfold Wf_cf in W0.
  destruct (malloc_cf_null_path n tr s trc s' (shape_cf_of_WfP_cf _ _ _ _ _ W0) Hp Hg) as (_ & _ & Hprim & _).
  pose proof (PresetCfnA.preset_no_refusal U sm x H0 s n tr true W Hx RAF Hprim) as R.
  pose proof (PRH_Base.prh_rpost_granted _ _ _ trc (PNull, s') R Hp Hg) as G.
  cbv beta in G. discriminate (G eq_refl).
Qed.

Lemma prh_refute_follow : forall U sm x H0 s,
  Wf_cf U s -> Z.of_nat (length x) <= PresetReqAt.MAXB -> PresetCfnA.run_allocs_follow sm x H0 s ->
  prh_granted_null s -> False.
Proof.
  intros U sm x H0 s W Hx RAF [(n & tr & trc & s' & Hp & Hg) | (n & tr & s' & s1 & t1 & t2 & Hp1 & Hg1 & Hp2 & Hg2)].
  - exact (prh_refute_malloc_follow U sm x H0 s n tr trc s' W Hx RAF Hp Hg).
  - (* the entry free_cf PNull moves st_nev / st_internal_inited only: Wf_cf and the position are kept *)
    destruct (PresetRoomPosKeep.rp_frame_null U tr s t1 tt s1 W Hp1) as (W1 & _ & _ & _ & _ & _ & _ & Kp).
    destruct RAF as (os & i & hist & Hpos & Hc & Ha).
    rewrite prh_gflag_eq in Hg2.
    apply (prh_refute_malloc_follow U sm x H0 s1 n tr t2 s' W1 Hx); [|exact Hp2|exact Hg2].
    exists os, i, hist. exact (conj (Kp sm x os i H0 hist Hpos) (conj Hc Ha)).
Qed.

(* ---- AT A POSITION OF THE RUN: the run's event at i is an allocation and a consumer one, and the walk holds the
   position at the call's own state; that is run_allocs_follow (and the run is not empty, so |x| <= MAXB) ---- *)
Lemma prh_follow_of_pos : forall sm x os i e H0 hist s,
  PresetRoomPos.iface_room_pos sm x os i H0 hist s ->
  nth_error (PresetRun.hruns sm x os) i = Some e -> PresetSite17.is_alloc e = true ->
  nth i (PresetRun.hcons sm x os) false = true ->
  Z.of_nat (length x) <= PresetReqAt.MAXB /\ PresetCfnA.run_allocs_follow sm x H0 s.
Proof.
  intros sm x os i e H0 hist s Hpos He Ha Hc. split.
  - destruct (Z_le_gt_dec (Z.of_nat (length x)) PresetReqAt.MAXB) as [H|H]; [exact H|].
    rewrite (PresetRoomCounts.iface_hruns_big sm x os ltac:(lia)) in He. destruct i; cbn in He; discriminate He.
  - exists os, i, hist. split; [exact Hpos|]. split; [exact Hc|].
    unfold PresetSite17.alloc_at. rewrite He. exact Ha.
Qed.

(* THE FAMILY'S SHAPE: a consumer window from i whose first event is an allocation, the position at i at the call's
   state, and the machine-level refusal there - impossible *)
Lemma prh_refute_at : forall U sm x os i k e H0 hist s,
  PRH_Base.prh_cons_from sm x os i k -> (0 < k)%nat ->
  nth_error (PresetRun.hruns sm x os) i = Some e -> PresetSite17.is_alloc e = true ->
  PresetRoomPos.iface_room_pos sm x os i H0 hist s -> Wf_cf U s -> prh_granted_null s -> False.
Proof.
  intros U sm x os i k e H0 hist s Hc Hk He Ha Hpos W N.
  assert (He0 : nth_error (PresetRun.hruns sm x os) (i + 0) = Some e) by (rewrite Nat.add_0_r; exact He).
  pose proof (prh_cons_at sm x os i k 0 e Hc Hk He0 Ha) as Hh. rewrite Nat.add_0_r in Hh.
  destruct (prh_follow_of_pos sm x os i e H0 hist s Hpos He Ha Hh) as [Hx RAF].
  exact (prh_refute_follow U sm x H0 s W Hx RAF N).
Qed.

(* the same at the j-th event of a text's own list E (its run premise and its consumer window at the entry i), the
   position i + j at the state of that event's allocator call *)
Lemma prh_refute_window : forall U sm x os i E j e H0 hist s,
  PRH_Base.prh_run_at sm x os i E -> PRH_Base.prh_cons_from sm x os i (length E) ->
  nth_error E j = Some e -> PresetSite17.is_alloc e = true ->
  PresetRoomPos.iface_room_pos sm x os (i + j) H0 hist s -> Wf_cf U s -> prh_granted_null s -> False.
Proof.
  intros U sm x os i E j e H0 hist s Hr Hc He Ha Hpos W N.
  assert (Hj : (j < length E)%nat) by (apply List.nth_error_Some; rewrite He; discriminate).
  pose proof (prh_run_at_nth sm x os i E j e Hr He) as Hn.
  pose proof (prh_cons_at sm x os i (length E) j e Hc Hj Hn Ha) as Hh.
  destruct (prh_follow_of_pos sm x os (i + j) e H0 hist s Hpos Hn Ha Hh) as [Hx RAF].
  exact (prh_refute_follow U sm x H0 s W Hx RAF N).
Qed.

(* ---- ONE PER CALLEE, over the callee's own list (the run premise and the consumer window its text takes at entry,
   or its caller's split of its own window by PRH_Base.prh_run_at_app_iff / prh_cons_from_app_iff) ---- *)

(* pj_string: its one allocation, the strdup's HMal, when the harness did not choose it to fail *)
Corollary prh_refute_pj_string : forall U sm x os i len cnt fail H0 hist s,
  PRH_Base.prh_run_at sm x os i (PRH_FnPj.prhPj_string_evs len cnt fail) ->
  PRH_Base.prh_cons_from sm x os i (length (PRH_FnPj.prhPj_string_evs len cnt fail)) -> cnt <> fail ->
  PresetRoomPos.iface_room_pos sm x os i H0 hist s -> Wf_cf U s -> prh_granted_null s -> False.
Proof.
  intros U sm x os i len cnt fail H0 hist s Hr Hc Hf Hpos W N.
  assert (E : PRH_FnPj.prhPj_string_evs len cnt fail = [PresetReqAt.HMal (len + 1 + cf_head)]).
  { unfold PRH_FnPj.prhPj_string_evs. rewrite (proj2 (Z.eqb_neq cnt fail) Hf). reflexivity. }
  rewrite E in Hr, Hc.
  apply (prh_refute_window U sm x os i _ 0 (PresetReqAt.HMal (len + 1 + cf_head)) H0 hist s Hr Hc eq_refl eq_refl);
    [rewrite Nat.add_0_r; exact Hpos | exact W | exact N].
Qed.

(* pj_set: any allocation of its list (absent key: grow's kids / keys reallocs, the key's strdup) *)
Corollary prh_refute_pj_set : forall U sm x os i ms kname n cap j e H0 hist s,
  PRH_Base.prh_run_at sm x os i (PRH_FnPj.prhPj_set_evs ms kname n cap) ->
  PRH_Base.prh_cons_from sm x os i (length (PRH_FnPj.prhPj_set_evs ms kname n cap)) ->
  nth_error (PRH_FnPj.prhPj_set_evs ms kname n cap) j = Some e -> PresetSite17.is_alloc e = true ->
  PresetRoomPos.iface_room_pos sm x os (i + j) H0 hist s -> Wf_cf U s -> prh_granted_null s -> False.
Proof.
  intros U sm x os i ms kname n cap j e H0 hist s Hr Hc He Ha Hpos W N.
  exact (prh_refute_window U sm x os i _ j e H0 hist s Hr Hc He Ha Hpos W N).
Qed.

(* pj_write: any grow of its all-granted list (each one fuzz_realloc of the buffer) *)
Corollary prh_refute_pj_write : forall U sm x os i cnt fail P j e H0 hist s,
  PRH_Base.prh_run_at sm x os i (PRH_FnWriter.prhWriter_pjw_evs [] cnt fail P) ->
  PRH_Base.prh_cons_from sm x os i (length (PRH_FnWriter.prhWriter_pjw_evs [] cnt fail P)) ->
  nth_error (PRH_FnWriter.prhWriter_pjw_evs [] cnt fail P) j = Some e -> PresetSite17.is_alloc e = true ->
  PresetRoomPos.iface_room_pos sm x os (i + j) H0 hist s -> Wf_cf U s -> prh_granted_null s -> False.
Proof.
  intros U sm x os i cnt fail P j e H0 hist s Hr Hc He Ha Hpos W N.
  exact (prh_refute_window U sm x os i _ j e H0 hist s Hr Hc He Ha Hpos W N).
Qed.

(* tx_put: its grow, in ttx_put_specX's own event premise (the raw realloc of the buffer to 2 * need) *)
Corollary prh_refute_tx_put : forall U sm x os i cap0 need H0 hist s,
  nth_error (PresetRun.hruns sm x os) i =
    Some (if cap0 =? 0 then PresetReqAt.HMal (2 * need) else PresetReqAt.HRe cap0 (2 * need)) ->
  PRH_Base.prh_cons_from sm x os i 1 ->
  PresetRoomPos.iface_room_pos sm x os i H0 hist s -> Wf_cf U s -> prh_granted_null s -> False.
Proof.
  intros U sm x os i cap0 need H0 hist s He Hc Hpos W N.
  apply (prh_refute_at U sm x os i 1 _ H0 hist s Hc ltac:(lia) He); [|exact Hpos | exact W | exact N].
  destruct (cap0 =? 0); reflexivity.
Qed.

(* tx_string / tx_line / tx_value: any grow of their puts (PRH_FnTx.prhtx_evs) *)
Corollary prh_refute_tx : forall U sm x os i len0 cap0 ks j e H0 hist s,
  PRH_Base.prh_run_at sm x os i (PRH_FnTx.prhtx_evs len0 cap0 ks) ->
  PRH_Base.prh_cons_from sm x os i (length (PRH_FnTx.prhtx_evs len0 cap0 ks)) ->
  nth_error (PRH_FnTx.prhtx_evs len0 cap0 ks) j = Some e -> PresetSite17.is_alloc e = true ->
  PresetRoomPos.iface_room_pos sm x os (i + j) H0 hist s -> Wf_cf U s -> prh_granted_null s -> False.
Proof.
  intros U sm x os i len0 cap0 ks j e H0 hist s Hr Hc He Ha Hpos W N.
  exact (prh_refute_window U sm x os i _ j e H0 hist s Hr Hc He Ha Hpos W N).
Qed.

(* parse_noting (and pj_parse under it): any allocation of the ALL-GRANTED reading's events (the list of its outcome
   clause; call_rest's reading is consumer, check_no_overread's three P1 readings are not) *)
Corollary prh_refute_parse_noting : forall U sm x os i tb j e H0 hist s,
  PRH_Base.prh_run_at sm x os i (PresetReqAt.parse_evs ReaderRes.jr_strtod tb []) ->
  PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.parse_evs ReaderRes.jr_strtod tb [])) ->
  nth_error (PresetReqAt.parse_evs ReaderRes.jr_strtod tb []) j = Some e -> PresetSite17.is_alloc e = true ->
  PresetRoomPos.iface_room_pos sm x os (i + j) H0 hist s -> Wf_cf U s -> prh_granted_null s -> False.
Proof.
  intros U sm x os i tb j e H0 hist s Hr Hc He Ha Hpos W N.
  exact (prh_refute_window U sm x os i _ j e H0 hist s Hr Hc He Ha Hpos W N).
Qed.

End rf.

(* ---- THE TEXT LEVEL, pj_write (the rtt102 walk's need at round_trip_text's first exit): tpj_write_specX's DEAD-PJWRITE
   (prh_granted over the ok its post binds) and no chosen failure among its k calls give w_failed st' = 0, so its
   failed arm (w_failed st' <> 0, q = 0) is refuted. The window is the leaves' pick condition with the counter's
   wrap excluded: `cnt + k <= fail` (fail = SIZE_MAXZ at round_trip_text / check_round_trip), or `fail < cnt` with
   cnt + k <= 2 ^ 64. ---- *)
Lemma prh_wput1_calls : forall st b, exists l, WriterApp.w_calls (WriterApp.put1 st b) = WriterApp.w_calls st ++ l.
Proof.
  intros st b. unfold WriterApp.put1.
  destruct (negb (WriterApp.w_failed st =? 0)); [exists []; rewrite app_nil_r; reflexivity|].
  cbv zeta. destruct (_ <=? _); [exists []; rewrite app_nil_r; reflexivity|].
  destruct (_ =? _); eexists; cbn [WriterApp.w_calls]; reflexivity.
Qed.

Lemma prh_put1_calls_grow : forall okb st b, PRH_FnWriter.prhWriter_grows st b = true ->
  exists c, WriterApp.w_calls (PRH_FnWriter.prhWriter_put1 okb st b) = WriterApp.w_calls st ++ [c].
Proof.
  intros okb st b G. unfold PRH_FnWriter.prhWriter_put1. rewrite G. cbv zeta.
  destruct (_ =? _), okb; eexists; cbn [WriterApp.w_calls]; reflexivity.
Qed.

Lemma prh_putN_calls : forall P ok st, exists l,
  WriterApp.w_calls (PRH_FnWriter.prhWriter_putN ok st P) = WriterApp.w_calls st ++ l.
Proof.
  induction P as [|b P IH]; intros ok st; cbn [PRH_FnWriter.prhWriter_putN].
  - exists []. rewrite app_nil_r. reflexivity.
  - destruct (PRH_FnWriter.prhWriter_grows st b) eqn:G.
    + destruct (IH (tl ok) (PRH_FnWriter.prhWriter_put1 (hd true ok) st b)) as [l Hl].
      destruct (prh_put1_calls_grow (hd true ok) st b G) as [c Hc].
      rewrite Hl, Hc, <- app_assoc. eexists. reflexivity.
    + destruct (IH ok (WriterApp.put1 st b)) as [l Hl]. destruct (prh_wput1_calls st b) as [l1 H1].
      rewrite Hl, H1, <- app_assoc. eexists. reflexivity.
Qed.

(* a run of puts from an unfailed writer whose k calls are all granted and meet no pick stays unfailed *)
Lemma prh_putN_unfailed : forall P ok st,
  WriterApp.w_failed st = 0 -> 0 <= WriterApp.w_cnt st ->
  (forall i, (i < PRH_FnWriter.prhWriter_k ok st P)%nat ->
     WriterApp.w_cnt st + Z.of_nat i < 2 ^ 64 /\ WriterApp.w_cnt st + Z.of_nat i <> WriterApp.w_fail st /\
     nth i ok true = true) ->
  WriterApp.w_failed (PRH_FnWriter.prhWriter_putN ok st P) = 0.
Proof.
  induction P as [|b P IH]; intros ok st Hf Hc H; [exact Hf|].
  unfold PRH_FnWriter.prhWriter_k in H. cbn [PRH_FnWriter.prhWriter_putN] in H |- *.
  revert H. destruct (PRH_FnWriter.prhWriter_grows st b) eqn:G; intro H.
  - set (st1 := PRH_FnWriter.prhWriter_put1 (hd true ok) st b) in *.
    destruct (prh_putN_calls P (tl ok) st1) as [l Hl].
    destruct (prh_put1_calls_grow (hd true ok) st b G) as [c C1]. fold st1 in C1.
    rewrite Hl, C1, !length_app in H. cbn [length] in H.
    destruct (H 0%nat ltac:(lia)) as (H0a & H0b & H0c).
    change (Z.of_nat 0) with 0 in H0a, H0b. rewrite Z.add_0_r in H0a, H0b.
    assert (Hok : hd true ok = true) by (destruct ok; [reflexivity | exact H0c]).
    assert (F1 : WriterApp.w_failed st1 = 0 /\ WriterApp.w_cnt st1 = (WriterApp.w_cnt st + 1) mod 2 ^ 64 /\
                 WriterApp.w_fail st1 = WriterApp.w_fail st).
    { unfold st1, PRH_FnWriter.prhWriter_put1. rewrite G, Hok. cbv zeta.
      rewrite (proj2 (Z.eqb_neq _ _) H0b). cbn [WriterApp.w_failed WriterApp.w_cnt WriterApp.w_fail].
      repeat split; reflexivity. }
    destruct F1 as (F1 & F2 & F3).
    apply IH; [exact F1 | rewrite F2; apply Z.mod_pos_bound; lia |].
    intros i Hi. unfold PRH_FnWriter.prhWriter_k in Hi. rewrite Hl, length_app in Hi.
    destruct (H (Datatypes.S i) ltac:(lia)) as (A1 & A2 & A3).
    rewrite Nat2Z.inj_succ in A1, A2.
    rewrite F2, F3, Z.mod_small by lia.
    split; [lia|]. split; [lia|].
    destruct ok as [|o ok']; [destruct i; reflexivity | exact A3].
  - assert (Hg : (WriterApp.w_cap st <? PRH_FnWriter.prhWriter_need st b) = false).
    { unfold PRH_FnWriter.prhWriter_grows in G. rewrite Hf in G. exact G. }
    apply Z.ltb_ge in Hg. unfold PRH_FnWriter.prhWriter_need in Hg.
    assert (E2 : WriterApp.put1 st b = WriterApp.mkW 0 (WriterApp.w_text st ++ b) (WriterApp.w_cap st)
                   (WriterApp.w_cnt st) (WriterApp.w_fail st) (WriterApp.w_calls st)).
    { unfold WriterApp.put1. rewrite Hf. change (negb (0 =? 0)) with false. cbv iota zeta.
      rewrite (proj2 (Z.leb_le _ _) Hg). reflexivity. }
    rewrite E2 in H |- *.
    apply IH; [reflexivity | exact Hc |].
    intros i Hi. unfold PRH_FnWriter.prhWriter_k in Hi. cbn [WriterApp.w_calls] in Hi.
    exact (H i Hi).
Qed.

Lemma prh_refute_pj_write_failed : forall ok cnt fail P,
  0 <= cnt -> fail < 2 ^ 64 ->
  (cnt + Z.of_nat (PRH_FnWriter.prhWriter_k ok (WriterApp.w0 cnt fail) P) <= fail \/
   fail < cnt /\ cnt + Z.of_nat (PRH_FnWriter.prhWriter_k ok (WriterApp.w0 cnt fail) P) <= 2 ^ 64) ->
  PRH_Base.prh_granted ok cnt fail (PRH_FnWriter.prhWriter_k ok (WriterApp.w0 cnt fail) P) ->
  WriterApp.w_failed (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 cnt fail) P) = 0.
Proof.
  intros ok cnt fail P Hc Hf Hw G.
  apply prh_putN_unfailed; [reflexivity | exact Hc |].
  intros i Hi. cbn [WriterApp.w0 WriterApp.w_cnt WriterApp.w_fail].
  assert (A : cnt + Z.of_nat i < 2 ^ 64 /\ cnt + Z.of_nat i <> fail) by lia.
  destruct A as [A1 A2]. split; [exact A1|]. split; [exact A2|].
  destruct (nth i ok true) eqn:E; [reflexivity|]. exfalso. exact (A2 (G i Hi E)).
Qed.
