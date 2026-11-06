(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatSim StoreOk.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import ArtMem EbtPoison ArtRuns EbtCls EbtFp ArtBridge EbtRecycle1 EbtRecycle2C EbrRcy5A EbrRcy5I EbrRcy5T EbrRcy5C EbrInvRecycleA EbrInvRecycleD.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import EbtInitCache EbtCls EbtRecycle3L EbrRcy3R EbrRcy3L.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import EbrInv EbrCreditT.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
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

#[using="Type"] Lemma art_cls_events_cost : forall spb c w cl, 1 <= c <= 30 -> art_cost_sum (art_cls_events spb c cl) = art_cl_maps (art_cls_dealloc c w cl) - art_cl_maps cl.
Proof.
  intros spb c w cl Hc. destruct (art_ic_mc_half c ltac:(lia)) as (_ & Hh).
  unfold art_cl_maps, art_cls_events, art_cls_dealloc, art_rta_events. destruct (art_cls_full c cl); [|cbn; lia].
  cbn [art_cls_push art_cls_return cl_mu cl_mfa]. rewrite art_cls_mfa'_grow, Z2Nat.id by lia.
  destruct (4 * (Z.of_nat (length (cl_free cl)) + art_ic_mc c / 2) <=? cl_mfa cl) eqn:E.
  - apply Z.leb_le in E. rewrite art_mfa_grow_warm by exact E. cbn. lia.
  - cbn [art_cost_sum fold_right art_cost]. lia.
Qed.

#[using="Type"] Lemma art_cls_events_evok : forall spb qs kbase c w cl log, 1 <= c <= 30 -> art_cls_ok c cl -> spb = 65536 * qs -> kbase < spb -> spb <= kbase + 65536 -> In (kbase, 0x2000011000) RESV ->
  (art_cls_full c cl = true -> 4 * (Z.of_nat (length (cl_free cl)) + art_ic_mc c / 2) <= 2 ^ 29) ->
  art_cost_sum log + (art_cl_maps (art_cls_dealloc c w cl) - art_cl_maps cl) <= BUDGET ->
  art_evok_list EVOK log (art_cls_events spb c cl).
Proof.
  intros spb qs kbase c w cl log Hc OK Espb Hk1 Hk2 HRES Room HB.
  rewrite <- (art_cls_events_cost spb c w cl Hc) in HB.
  destruct (art_ic_mc_half c ltac:(lia)) as (_ & Hh).
  pose proof OK as (_ & _ & _ & _ & _ & _ & (kf & Emfa) & (Hmfa0 & Hmfa1) & _).
  unfold art_cls_events, art_rta_events in *. destruct (art_cls_full c cl); [|exact I]. specialize (Room eq_refl).
  destruct (4 * (Z.of_nat (length (cl_free cl)) + art_ic_mc c / 2) <=? cl_mfa cl) eqn:E; [exact I|]. apply Z.leb_gt in E.
  destruct (art_mfa_grow_cold (cl_mfa cl) (Z.of_nat (length (cl_free cl)) + art_ic_mc c / 2) E Hmfa0) as (q & rr & Eq & Hrr & Eg & Hq).
  pose proof (art_mfa_grow_le (cl_mfa cl) (Z.of_nat (length (cl_free cl)) + art_ic_mc c / 2) kf Emfa (conj Hmfa0 Hmfa1) ltac:(lia) Room) as Hle.
  rewrite Eg in *. cbn [art_evok_list]. split; [|exact I]. cbn [art_EVOK].
  split. { rewrite Espb, Emfa. replace (65536 * qs + c * 2 ^ 32 + 3758096384 + 262144 * kf) with ((16 * qs + c * 2 ^ 20 + 917504 + 64 * kf) * 4096) by lia. apply Z_mod_mult. }
  split. { rewrite Emfa. replace (262144 * q - 262144 * kf) with ((64 * (q - kf)) * 4096) by lia. apply Z_mod_mult. }
  split; [lia|]. split; [exists (kbase, 0x2000011000); cbn [fst snd]; split; [exact HRES|lia]|].
  rewrite art_cost_sum_snoc. cbn [art_cost]. cbn [art_cost_sum fold_right art_cost] in HB. lia.
Qed.

Definition art_rcy_cls (G : art_rg) (nt : Z) : Prop :=
  forall c, 1 <= c <= 30 -> art_cls_ok c (rg_cls G c) /\ Z.of_nat (length (cl_cache (rg_cls G c))) <= art_ic_mc c
                            /\ Z.of_nat (length (cl_cache (rg_cls G c))) + Z.of_nat (length (cl_free (rg_cls G c))) + nt <= 134217720.
#[using="Type"] Lemma art_rcy_cls_room : forall G nt c, 0 <= nt -> art_rcy_cls G (nt + 1) -> 1 <= c <= 30 ->
  art_cls_full c (rg_cls G c) = true -> 4 * (Z.of_nat (length (cl_free (rg_cls G c))) + art_ic_mc c / 2) <= 2 ^ 29.
Proof.
  intros G nt c Hnt CLS Hc EF. destruct (CLS c Hc) as (_ & _ & CNT). destruct (art_ic_mc_half c ltac:(lia)) as (Emc & Hh).
  unfold art_cls_full in EF. apply Z.eqb_eq in EF. lia.
Qed.
#[using="Type"] Lemma art_rcy_cls_step : forall e G nt, 0 <= nt -> art_rcy_cls G (nt + 1) -> art_rel_pre G e -> art_rcy_cls (art_rel_step e G) nt.
Proof.
  intros e G nt Hnt CLS PRE c Hc. destruct (CLS c Hc) as (OK & LE & CNT).
  assert (DEA : forall c0 w0, 1 <= c0 <= 30 -> art_cptr_ok (AsanTab.class_size c0) (cl_au (rg_cls G c0)) w0 -> ~ In w0 (cl_cache (rg_cls G c0) ++ cl_free (rg_cls G c0)) ->
                art_cls_ok c0 (art_cls_dealloc c0 w0 (rg_cls G c0)) /\ Z.of_nat (length (cl_cache (art_cls_dealloc c0 w0 (rg_cls G c0)))) <= art_ic_mc c0
                /\ Z.of_nat (length (cl_cache (art_cls_dealloc c0 w0 (rg_cls G c0)))) + Z.of_nat (length (cl_free (art_cls_dealloc c0 w0 (rg_cls G c0)))) + nt <= 134217720).
  { intros c0 w0 Hc0 Hw Hn. destruct (CLS c0 Hc0) as (OK0 & LE0 & CNT0).
    split; [apply art_cls_dealloc_ok; [exact Hc0|exact OK0|exact LE0|exact Hw|exact Hn|exact (art_rcy_cls_room G nt c0 Hnt CLS Hc0)]|].
    split; [apply art_cls_dealloc_cache_le; [exact LE0|lia]|]. pose proof (art_cls_dealloc_total c0 w0 (rg_cls G c0) LE0 ltac:(lia)). lia. }
  destruct e as [c0 w0 d0 b10 n0|mb0 ms0 m0 b10 n0|wb0]; cbn [art_rel_step rg_cls art_rel_pre] in *.
  - destruct PRE as (Hc0 & Hw & Hn & _). destruct (Z.eq_dec c c0) as [->|NE]; [rewrite art_cls_upd_same; exact (DEA c0 w0 Hc0 Hw Hn)|rewrite art_cls_upd_other by exact NE].
    split; [exact OK|]. split; [exact LE|lia].
  - split; [exact OK|]. split; [exact LE|lia].
  - destruct PRE as (Hw & Hn). destruct (Z.eq_dec c 24) as [->|NE]; [rewrite art_cls_upd_same; apply (DEA 24 wb0 ltac:(lia)); [exact Hw|exact Hn]|rewrite art_cls_upd_other by exact NE].
    split; [exact OK|]. split; [exact LE|lia].
Qed.

#[using="Type"] Lemma art_rel_events_cost : forall spb e G, art_rel_pre G e -> art_cost_sum (art_rel_events spb G e) = art_primsum (rg_cls (art_rel_step e G)) - art_primsum (rg_cls G).
Proof.
  intros spb e G PRE. destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_events art_rel_step rg_cls art_rel_pre] in *.
  - destruct PRE as (Hc & _). unfold art_cls_upd. rewrite (art_primsum_upd (rg_cls G) c _ Hc), (art_cls_events_cost spb c w (rg_cls G c) Hc). lia.
  - assert (X : art_cost_sum (art_flush_events mb ms ++ [AMunmap mb ms]) = 0).
    { unfold art_flush_events. destruct (art_flush_beg mb <? art_flush_end mb ms); reflexivity. }
    rewrite X. lia.
  - unfold art_cls_upd. rewrite (art_primsum_upd (rg_cls G) 24 _ ltac:(lia)), (art_cls_events_cost spb 24 wb (rg_cls G 24) ltac:(lia)). lia.
Qed.
#[using="Type"] Lemma art_cost_sum_app : forall l1 l2, art_cost_sum (l1 ++ l2) = art_cost_sum l1 + art_cost_sum l2.
Proof. induction l1 as [|a r IH]; intros l2; [reflexivity|]. cbn [app]. unfold art_cost_sum in *. cbn [fold_right]. rewrite IH. apply Z.add_assoc. Qed.
#[using="Type"] Lemma art_rels_events_cost : forall spb work G, art_rels_pre G work ->
  art_cost_sum (art_rels_events spb G work) = art_primsum (rg_cls (art_rel_steps work G)) - art_primsum (rg_cls G).
Proof.
  intros spb. induction work as [|e r IH]; intros G PRE; [cbn; lia|]. destruct PRE as (Pe & Pr).
  cbn [art_rels_events]. rewrite art_cost_sum_app, (art_rel_events_cost spb e G Pe), (IH _ Pr). unfold art_rel_steps. cbn [fold_left]. lia.
Qed.

#[using="Type"] Lemma art_rcy_evok : forall spb qs kbase CB work G log,
  (forall mb ms m b1 n, In (RES mb ms m b1 n) work -> In (mb, ms) (art_live log) /\ mb mod 4096 = 0 /\ ms mod 4096 = 0 /\ 0 <= mb /\ 0 <= ms) ->
  List.NoDup (map art_rel_key work) ->
  spb = 65536 * qs -> kbase < spb -> spb <= kbase + 65536 -> In (kbase, 0x2000011000) RESV ->
  art_rels_pre G work -> art_rcy_cls G (Z.of_nat (length work)) ->
  art_cost_sum log <= CB + art_primsum (rg_cls G) -> CB + PRIMCAP <= BUDGET ->
  art_evok_list EVOK log (art_rels_events spb G work).
Proof.
  intros spb qs kbase CB. induction work as [|e r IH]; intros G log ALL ND Espb Hk1 Hk2 HRES PRE CLS HC HB; [exact I|]. cbn [art_rels_events].
  cbn [map] in ND. inversion ND as [|? ? Hn NDr]; subst. destruct PRE as (Pe & Pr).
  cbn [length] in CLS. replace (Z.of_nat (S (length r))) with (Z.of_nat (length r) + 1) in CLS by lia.
  pose proof (art_rcy_cls_step e G (Z.of_nat (length r)) ltac:(lia) CLS Pe) as CLS'.
  assert (PS' : art_primsum (rg_cls (art_rel_step e G)) <= PRIMCAP) by (apply art_primsum_le; intros c Hc; exact (proj1 (CLS' c Hc))).
  pose proof (art_rel_events_cost (65536 * qs) e G Pe) as CE.
  apply art_evok_list_app. split.
  - destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_events art_rel_step rg_cls art_rel_pre] in *.
    + destruct Pe as (Hc & _). destruct (CLS c Hc) as (OK & _).
      apply (art_cls_events_evok (65536 * qs) qs kbase c w (rg_cls G c) log Hc OK eq_refl Hk1 Hk2 HRES (art_rcy_cls_room G (Z.of_nat (length r)) c ltac:(lia) CLS Hc)).
      rewrite <- (art_cls_events_cost (65536 * qs) c w (rg_cls G c) Hc). lia.
    + destruct (ALL mb ms m b1 n (or_introl eq_refl)) as (Hl & A1 & A2 & P1 & P2).
      destruct (art_flush_range mb ms A1 A2 P1 P2) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _).
      unfold art_flush_events. destruct (art_flush_beg mb <? art_flush_end mb ms) eqn:EL; cbn [app art_evok_list].
      * apply Z.ltb_lt in EL. split.
        -- cbn [art_EVOK]. split; [exact F1|]. split; [exact F3|]. split; [lia|]. exists (art_shlo mb, art_shhi mb ms). split; [exact (art_log_window log mb ms (art_live_in_log log mb ms Hl))|]. cbn [fst snd]. lia.
        -- split; [|exact I]. cbn [art_EVOK]. rewrite art_live_snoc. cbn [art_ev_live]. exact Hl.
      * split; [|exact I]. cbn [art_EVOK]. exact Hl.
    + destruct (CLS 24 ltac:(lia)) as (OK & _).
      apply (art_cls_events_evok (65536 * qs) qs kbase 24 wb (rg_cls G 24) log ltac:(lia) OK eq_refl Hk1 Hk2 HRES (art_rcy_cls_room G (Z.of_nat (length r)) 24 ltac:(lia) CLS ltac:(lia))).
      rewrite <- (art_cls_events_cost (65536 * qs) 24 wb (rg_cls G 24) ltac:(lia)). lia.
  - apply IH; [|exact NDr|reflexivity|exact Hk1|exact Hk2|exact HRES|exact Pr|exact CLS'|rewrite art_cost_sum_app, CE; lia|exact HB].
    intros mb ms m b1 n Hin. destruct (ALL mb ms m b1 n (or_intror Hin)) as (Hl & REST). split; [|exact REST].
    destruct e as [c0 w0 d0 b10 n0|mb0 ms0 m0 b10 n0|wb0]; cbn [art_rel_events]; rewrite ?art_live_cls_events; try exact Hl.
    rewrite art_live_app_unmap. apply filter_In. split; [exact Hl|]. cbn [fst]. apply negb_true_iff, Z.eqb_neq. intros E. apply Hn. cbn [art_rel_key]. rewrite <- E.
    apply in_map_iff. exists (RES mb ms m b1 n). split; [reflexivity|exact Hin].
Qed.
End Evok.

Lemma art_rels_events_kinds : forall spb work G ev, In ev (art_rels_events spb G work) ->
  (exists a l, ev = AMadvise a l) \/ (exists a l, ev = AMunmap a l) \/ (exists a l, ev = AMmapFixed a l).
Proof.
  intros spb. induction work as [|e r IH]; intros G ev H; [destruct H|]. cbn [art_rels_events] in H. apply in_app_or in H. destruct H as [H|H]; [|exact (IH _ ev H)].
  assert (CE : forall c cl, In ev (art_cls_events spb c cl) -> exists a l, ev = AMmapFixed a l).
  { intros c cl X. unfold art_cls_events, art_rta_events in X. destruct (art_cls_full c cl); [|destruct X]. destruct (_ <=? _); [destruct X|]. destruct X as [<-|[]]. eexists; eexists; reflexivity. }
  destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_events] in H; [right; right; exact (CE _ _ H)| |right; right; exact (CE _ _ H)].
  apply in_app_or in H. destruct H as [H|[<-|[]]]; [|right; left; eexists; eexists; reflexivity].
  unfold art_flush_events in H. destruct (art_flush_beg mb <? art_flush_end mb ms); [destruct H as [<-|[]]; left; eexists; eexists; reflexivity|destruct H].
Qed.

Lemma art_live_rcy_len : forall spb work G log, (length (art_live (log ++ art_rels_events spb G work)) <= length (art_live log))%nat.
Proof.
  intros spb. induction work as [|e r IH]; intros G log; [cbn [art_rels_events]; rewrite app_nil_r; lia|].
  cbn [art_rels_events]. rewrite app_assoc. specialize (IH (art_rel_step e G) (log ++ art_rel_events spb G e)).
  destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_events] in *; rewrite ?art_live_cls_events in *; try exact IH.
  rewrite art_live_app_unmap in IH. pose proof (filter_length_le (fun p : Z * Z => negb (fst p =? mb)) (art_live log)). lia.
Qed.

Lemma art_rcy_ev_range : forall spb work G ev z,
  (forall mb ms m b1 n, In (RES mb ms m b1 n) work -> mb mod 4096 = 0 /\ ms mod 4096 = 0 /\ 0 <= mb /\ 0 <= ms) ->
  art_rels_pre G work -> art_rcy_cls G (Z.of_nat (length work)) ->
  In ev (art_rels_events spb G work) -> fst (art_ev_range ev) <= z < snd (art_ev_range ev) ->
  (exists mb ms m b1 n, In (RES mb ms m b1 n) work /\ (mb <= z < mb + ms \/ SB + mb / 8 <= z < SB + mb / 8 + ms / 8))
  \/ (exists c, 1 <= c <= 30 /\ spb + c * 2 ^ 32 + 3758096384 <= z < spb + c * 2 ^ 32 + 2 ^ 32).
Proof.
  intros spb. induction work as [|e r IH]; intros G ev z ALL PRE CLS Hev Hz; [destruct Hev|]. destruct PRE as (Pe & Pr).
  cbn [length] in CLS. replace (Z.of_nat (S (length r))) with (Z.of_nat (length r) + 1) in CLS by lia.
  cbn [art_rels_events] in Hev. apply in_app_or in Hev. destruct Hev as [Hev|Hev].
  - assert (CE : forall c, 1 <= c <= 30 -> In ev (art_cls_events spb c (rg_cls G c)) -> spb + c * 2 ^ 32 + 3758096384 <= z < spb + c * 2 ^ 32 + 2 ^ 32).
    { intros c Hc X. destruct (CLS c Hc) as (OK & _). pose proof OK as (_ & _ & _ & _ & _ & _ & (kf & Emfa) & (Hmfa0 & Hmfa1) & _).
      destruct (art_ic_mc_half c ltac:(lia)) as (_ & Hh). pose proof (art_rcy_cls_room G (Z.of_nat (length r)) c ltac:(lia) CLS Hc) as Room.
      unfold art_cls_events, art_rta_events in X. destruct (art_cls_full c (rg_cls G c)); [|destruct X]. specialize (Room eq_refl).
      destruct (_ <=? _) eqn:E; [destruct X|]. apply Z.leb_gt in E. destruct X as [<-|[]]. cbn [art_ev_range fst snd] in Hz.
      pose proof (art_mfa_grow_le (cl_mfa (rg_cls G c)) (Z.of_nat (length (cl_free (rg_cls G c))) + art_ic_mc c / 2) kf Emfa (conj Hmfa0 Hmfa1) ltac:(lia) Room) as Hle. lia. }
    destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_events art_rel_pre] in *.
    + right. exists c. destruct Pe as (Hc & _). split; [exact Hc|exact (CE c Hc Hev)].
    + left. exists mb, ms, m, b1, n. split; [left; reflexivity|].
      destruct (ALL mb ms m b1 n (or_introl eq_refl)) as (A1 & A2 & P1 & P2). destruct (art_flush_range mb ms A1 A2 P1 P2) as (F1 & F2 & F3 & F4 & F5 & F6 & _).
      apply in_app_or in Hev. destruct Hev as [Hev|[<-|[]]]; [|left; cbn [art_ev_range fst snd] in Hz; exact Hz].
      unfold art_flush_events in Hev. destruct (art_flush_beg mb <? art_flush_end mb ms); [|destruct Hev]. destruct Hev as [<-|[]]. cbn [art_ev_range fst snd] in Hz. right. lia.
    + right. exists 24. split; [lia|exact (CE 24 ltac:(lia) Hev)].
  - destruct (IH (art_rel_step e G) ev z (fun mb ms m b1 n H => ALL mb ms m b1 n (or_intror H)) Pr (art_rcy_cls_step e G (Z.of_nat (length r)) ltac:(lia) CLS Pe) Hev Hz) as [(mb & ms & m & b1 & n & Hin & Hr)|X]; [left|right; exact X].
    exists mb, ms, m, b1, n. split; [right; exact Hin|exact Hr].
Qed.
