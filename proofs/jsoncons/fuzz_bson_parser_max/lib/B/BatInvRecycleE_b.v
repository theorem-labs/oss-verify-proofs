(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk As0Tables ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatPoison_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatRecycle1_b BatRecycle2C_b BatRecycle5A_b BatRecycle5I_b BatRecycle5T_b BatRecycle5C_b BatInvRecycleA_b BatInvRecycleD_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

Lemma art_live_in_log : forall log r len, In (r, len) (art_live log) -> In (AMmapNull len r) log.
Proof.
  intros log. induction log as [|ev l IH] using rev_ind; intros r len H; [destruct H|]. rewrite art_live_snoc in H. apply in_or_app.
  destruct ev as [a l0|l0 r0|a l0|a l0|a l0]; cbn [art_ev_live] in H; try (left; exact (IH r len H)).
  - destruct H as [E|H]; [right; left; injection E as -> ->; reflexivity|left; exact (IH r len H)].
  - apply filter_In in H. left. exact (IH r len (proj1 H)).
Qed.

Lemma art_log_window : forall log r len, In (AMmapNull len r) log -> In (art_shlo r, art_shhi r len) (art_windows log).
Proof. intros log r len H. unfold art_windows. apply in_flat_map. exists (AMmapNull len r). split; [exact H|left; reflexivity]. Qed.

Lemma art_windows_app : forall l1 l2 w, In w (art_windows l1) -> In w (art_windows (l1 ++ l2)).
Proof. intros l1 l2 w H. unfold art_windows in *. rewrite flat_map_app. apply in_or_app. left. exact H. Qed.

Section Evok.
Variable RESV : list (Z * Z).
Variables BUDGET LENMAX KMAX : Z.
#[local] Abbreviation EVOK := (art_EVOK RESV BUDGET LENMAX KMAX).

#[using="Type"] Lemma art_rcy_evok : forall work log,
  (forall mb ms m b1 n, In (RES mb ms m b1 n) work -> In (mb, ms) (art_live log) /\ mb mod 4096 = 0 /\ ms mod 4096 = 0 /\ 0 <= mb /\ 0 <= ms) ->
  List.NoDup (map art_rel_key work) -> art_evok_list EVOK log (art_rels_events work).
Proof.
  induction work as [|e r IH]; intros log ALL ND; [exact I|]. change (art_rels_events (e :: r)) with (art_rel_events e ++ art_rels_events r).
  cbn [map] in ND. inversion ND as [|? ? Hn NDr]; subst. apply art_evok_list_app. split.
  - destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_events]; try exact I.
    destruct (ALL mb ms m b1 n (or_introl eq_refl)) as (Hl & A1 & A2 & P1 & P2).
    destruct (art_flush_range mb ms A1 A2 P1 P2) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _).
    unfold art_flush_events. destruct (art_flush_beg mb <? art_flush_end mb ms) eqn:EL; cbn [app art_evok_list].
    + apply Z.ltb_lt in EL. split.
      * cbn [art_EVOK]. split; [exact F1|]. split; [exact F3|]. split; [lia|]. exists (art_shlo mb, art_shhi mb ms). split; [exact (art_log_window log mb ms (art_live_in_log log mb ms Hl))|]. cbn [fst snd]. lia.
      * split; [|exact I]. cbn [art_EVOK]. rewrite art_live_snoc. cbn [art_ev_live]. exact Hl.
    + split; [|exact I]. cbn [art_EVOK]. exact Hl.
  - apply IH; [|exact NDr]. intros mb ms m b1 n Hin. destruct (ALL mb ms m b1 n (or_intror Hin)) as (Hl & REST). split; [|exact REST].
    destruct e as [c0 w0 d0 b10 n0|mb0 ms0 m0 b10 n0|wb0]; cbn [art_rel_events]; rewrite ?app_nil_r; try exact Hl.
    rewrite art_live_app_unmap. apply filter_In. split; [exact Hl|]. cbn [fst]. apply negb_true_iff, Z.eqb_neq. intros E. apply Hn. cbn [art_rel_key]. rewrite <- E.
    apply in_map_iff. exists (RES mb ms m b1 n). split; [reflexivity|exact Hin].
Qed.
End Evok.

Lemma art_rels_events_kinds : forall work ev, In ev (art_rels_events work) -> (exists a l, ev = AMadvise a l) \/ (exists a l, ev = AMunmap a l).
Proof.
  intros work ev H. unfold art_rels_events in H. apply in_flat_map in H. destruct H as (e & _ & H).
  destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_events] in H; try destruct H. apply in_app_or in H. destruct H as [H|[<-|[]]]; [|right; eexists; eexists; reflexivity].
  unfold art_flush_events in H. destruct (art_flush_beg mb <? art_flush_end mb ms); [destruct H as [<-|[]]; left; eexists; eexists; reflexivity|destruct H].
Qed.

Lemma art_rels_events_cost : forall work, art_cost_sum (art_rels_events work) = 0.
Proof.
  intros work. assert (H : forall l, (forall ev, In ev l -> art_cost ev = 0) -> art_cost_sum l = 0).
  { induction l as [|a r IH]; intros A; [reflexivity|]. cbn [art_cost_sum fold_right]. rewrite (A a (or_introl eq_refl)). unfold art_cost_sum in IH. rewrite IH; [reflexivity|]. intros ev Hev. apply A. right. exact Hev. }
  apply H. intros ev Hev. destruct (art_rels_events_kinds work ev Hev) as [(a & l & ->)|(a & l & ->)]; reflexivity.
Qed.

Lemma art_live_rcy_len : forall work log, (length (art_live (log ++ art_rels_events work)) <= length (art_live log))%nat.
Proof.
  induction work as [|e r IH]; intros log; [unfold art_rels_events; cbn [flat_map]; rewrite app_nil_r; lia|].
  change (art_rels_events (e :: r)) with (art_rel_events e ++ art_rels_events r). rewrite app_assoc. specialize (IH (log ++ art_rel_events e)).
  destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_events] in *; rewrite ?app_nil_r in *; try exact IH.
  rewrite art_live_app_unmap in IH. pose proof (filter_length_le (fun p : Z * Z => negb (fst p =? mb)) (art_live log)). lia.
Qed.

(* [comment removed for export] *)
Lemma art_rcy_ev_range : forall work ev z,
  (forall mb ms m b1 n, In (RES mb ms m b1 n) work -> mb mod 4096 = 0 /\ ms mod 4096 = 0 /\ 0 <= mb /\ 0 <= ms) ->
  In ev (art_rels_events work) -> fst (art_ev_range ev) <= z < snd (art_ev_range ev) ->
  exists mb ms m b1 n, In (RES mb ms m b1 n) work /\ (mb <= z < mb + ms \/ SB + mb / 8 <= z < SB + mb / 8 + ms / 8).
Proof.
  intros work ev z ALL Hev Hz. unfold art_rels_events in Hev. apply in_flat_map in Hev. destruct Hev as (e & He & Hev).
  destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_events] in Hev; try destruct Hev. exists mb, ms, m, b1, n. split; [exact He|].
  destruct (ALL mb ms m b1 n He) as (A1 & A2 & P1 & P2). destruct (art_flush_range mb ms A1 A2 P1 P2) as (F1 & F2 & F3 & F4 & F5 & F6 & _).
  apply in_app_or in Hev. destruct Hev as [Hev|[<-|[]]]; [|left; cbn [art_ev_range fst snd] in Hz; exact Hz].
  unfold art_flush_events in Hev. destruct (art_flush_beg mb <? art_flush_end mb ms); [|destruct Hev]. destruct Hev as [<-|[]]. cbn [art_ev_range fst snd] in Hz. right. lia.
Qed.
