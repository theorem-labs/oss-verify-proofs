(* Theorem Labs, 2026-10: the RUN POSITION of parse_items' image-B walk in the POST-IMPLICATION form (b) of the reading
   chain (17:3xZ; the announced restatement: the run premise and the position move from the entry
   into the post, keyed on the bound outcomes, with exact advance; rp_ok dropped). PREPARED ahead of (b): no segment file
   uses it yet; when (b)'s texts land, PItems_pres.v's travelling position becomes pi_posb and the four event-form sites
   (entry, grow, parse_string, parse_value) compose through these lemmas only.
   THE SHAPE (as relayed for (b)): a callee whose trace is trc and whose states are S1 -> S2 gives
     forall sm x os i H0 hist, iface_room_pos sm x os i H0 hist S1 -> prh_run_at sm x os i (rd_hevs trc) ->
       exists hist', iface_room_pos sm x os (i + length (rd_hevs trc)) H0 hist' S2.
   pi_posb S Sc tr0 states the same relation from the function's ENTRY state S to the block state Sc for the events of
   the prefix trace tr0, so the function's own post is pi_posb S S' tr with tr its whole trace.
   Lemmas: pi_posb_nil (entry), pi_posb_eq (a step that keeps the allocator state), pi_posb_noev (an extension whose
   events are none, e.g. a refused grant), pi_posb_call (a callee in (b)'s form), and pi_posb_post (the function's post).
   THE HULL USE (route (b), lib/Spec/PresetHullBudget.v): pi_posb also states hull_used S Sc (rd_hevs tr0), the meters at
   Sc exceed the entry's by at most the prefix's counts. A callee's post gives its own use (pi_posb_call's hull
   premise); pi_posb_budget pays a callee from the entry budget; pi_posb_hull_post and pi_posb_hull_call give the
   function's post conjunct over its all-granted list (at the exit, and at a refused callee's exit).
   Rule 24: proves no function (kind: shared lemma). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Permutation.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjGrammar PresetReqAt PresetRoomPos PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget PresetSecTotal.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
Import ListNotations.

(* the position relation from the entry state S to the block state Sc, for the events of the prefix trace tr0, and the
   hull use over the same events *)
Definition pi_posb (S Sc : astate) (tr0 : list PjGrammar.ev) : Prop :=
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
  PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  prh_run_at sm x os i (PresetReqAt.rd_hevs tr0) ->
  exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs tr0))%nat H0 hist' Sc) /\
  PresetHullBudget.hull_used S Sc (PresetReqAt.rd_hevs tr0).

(* at the entry: no event yet *)
Lemma pi_posb_nil : forall S, pi_posb S S [].
Proof.
intros S. split; [|apply PresetHullBudget.hull_used_refl].
intros sm x os i H0 hist H _. exists hist. cbn [PresetReqAt.rd_hevs flat_map length]. rewrite Nat.add_0_r. exact H.
Qed.

(* a step that does not change the allocator state keeps it *)
Lemma pi_posb_eq : forall S Sc1 Sc2 tr0, Sc2 = Sc1 -> pi_posb S Sc1 tr0 -> pi_posb S Sc2 tr0.
Proof. intros S Sc1 Sc2 tr0 E H. rewrite E. exact H. Qed.

(* an extension of the trace that makes no event (a refused grant, a pure step) keeps it *)
Lemma pi_posb_noev : forall S Sc tr0 t, PresetReqAt.rd_hevs t = [] ->
  pi_posb S Sc tr0 -> pi_posb S Sc (tr0 ++ t).
Proof.
intros S Sc tr0 t Ht [H Hh]. unfold pi_posb. rewrite PresetReqAt.rd_hevs_app, Ht, app_nil_r. split; [|exact Hh].
intros sm x os i H0 hist Hi Hr. exact (H sm x os i H0 hist Hi Hr).
Qed.

(* a callee in (b)'s form, run from the block state Sc1 to Sc2 with trace trc, advances the block's relation; its
   post's hull use over the events of trc extends the block's *)
Lemma pi_posb_call : forall S Sc1 Sc2 tr0 trc,
  pi_posb S Sc1 tr0 ->
  (forall sm x os i H0 hist, PresetRoomPos.iface_room_pos sm x os i H0 hist Sc1 ->
     prh_run_at sm x os i (PresetReqAt.rd_hevs trc) ->
     exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs trc))%nat H0 hist' Sc2) ->
  PresetHullBudget.hull_used Sc1 Sc2 (PresetReqAt.rd_hevs trc) ->
  pi_posb S Sc2 (tr0 ++ trc).
Proof.
intros S Sc1 Sc2 tr0 trc [H0p Hh0] Hc Hhc. unfold pi_posb. rewrite PresetReqAt.rd_hevs_app.
split; [|exact (PresetHullBudget.hull_used_app _ _ _ _ _ Hh0 Hhc)].
intros sm x os i H0 hist Hi Hr.
apply prh_run_at_app_iff in Hr. destruct Hr as [Hr1 Hr2].
destruct (H0p sm x os i H0 hist Hi Hr1) as (hist1 & Hi1).
destruct (Hc sm x os _ H0 hist1 Hi1 Hr2) as (hist2 & Hi2).
exists hist2. rewrite length_app, Nat.add_assoc. exact Hi2.
Qed.

(* the function's own post conjunct in (b)'s form, from the relation at its exit with its whole trace *)
Lemma pi_posb_post : forall S S' tr, pi_posb S S' tr ->
  forall sm x os i H0 hist, PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  prh_run_at sm x os i (PresetReqAt.rd_hevs tr) ->
  exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs tr))%nat H0 hist' S'.
Proof. intros S S' tr H. exact (proj1 H). Qed.

(* ---- THE HULL USE ---- *)
(* the block's use since the entry *)
Lemma pi_posb_hull : forall S Sc tr0, pi_posb S Sc tr0 -> PresetHullBudget.hull_used S Sc (PresetReqAt.rd_hevs tr0).
Proof. intros S Sc tr0 H. exact (proj2 H). Qed.

(* the function's post conjunct at its exit: the use over its whole trace tr (under the instance's outcomes ok) is at
   most the all-granted list's (PresetHullBudget.hull_items_agrees) *)
Lemma pi_posb_hull_post : forall S S' sm d o x ok,
  pi_posb S S' (snd (fst (PjGrammar.jr_items sm d o x ok))) ->
  PresetHullBudget.hull_used S S' (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_items sm d o x [])))).
Proof.
intros S S' sm d o x ok H. destruct (PresetHullBudget.hull_items_agrees sm d o x ok) as [N T].
exact (PresetHullBudget.hull_used_weaken _ _ _ _ (proj2 H) N T).
Qed.

(* the function's post conjunct at a callee's exit (a refused callee): the block's use over the granted prefix E1,
   then the callee's own use over its all-granted list E2, are inside the whole all-granted list E1 ++ E2 ++ E3 *)
Lemma pi_posb_hull_call : forall S Sc S' tr0 E1 E2 E3, pi_posb S Sc tr0 -> PresetReqAt.rd_hevs tr0 = E1 ->
  PresetHullBudget.hull_used Sc S' E2 -> PresetHullBudget.hull_used S S' (E1 ++ E2 ++ E3).
Proof.
intros S Sc S' tr0 E1 E2 E3 H HE H2. pose proof (proj2 H) as Hh. rewrite HE in Hh.
pose proof (PresetHullBudget.hull_used_app _ _ _ _ _ Hh H2) as H12.
apply (PresetHullBudget.hull_used_weaken _ _ _ _ H12).
- rewrite !PresetSecTotal.nsec_app. lia.
- rewrite !PresetSecTotal.tsec_app. pose proof (PresetSecTotal.tsec_nn E3). lia.
Qed.

Section hb. Context {cp : YGcfNames.CfParams}.
(* a callee's budget at the block: its all-granted events E2 follow the prefix's E1 in the entry's list, and more
   events E3 may follow them (PresetHullBudget.hull_budget_infix) *)
Lemma pi_posb_budget : forall S Sc tr0 E1 E2 E3, PresetHullBudget.hull_budget S (E1 ++ E2 ++ E3) ->
  pi_posb S Sc tr0 -> PresetReqAt.rd_hevs tr0 = E1 -> PresetHullBudget.hull_budget Sc E2.
Proof.
intros S Sc tr0 E1 E2 E3 HB H HE. pose proof (proj2 H) as Hh. rewrite HE in Hh.
exact (PresetHullBudget.hull_budget_infix S Sc E1 E2 E3 HB Hh).
Qed.

(* a free's budget (no events): any block reached inside the entry's list has it *)
Lemma pi_posb_budget_nil : forall S Sc tr0 E1 E3, PresetHullBudget.hull_budget S (E1 ++ E3) ->
  pi_posb S Sc tr0 -> PresetReqAt.rd_hevs tr0 = E1 -> PresetHullBudget.hull_budget Sc [].
Proof.
intros S Sc tr0 E1 E3 HB H HE. exact (pi_posb_budget S Sc tr0 E1 [] E3 HB H HE).
Qed.
End hb.

(* ================================================================================================
   THE LIVE REQUESTS and THE LIVE COUNTS, f97c8b2f046b's other two halves (kit walkkit-next; the kit's
   tparse_items_specX 105eb463e190). The entry premise is a PEAK of a count along the ALL-GRANTED events of the
   whole call; the post states the live requests as the entry's moved by the events the instance MADE. A block of
   the walk carries pi_live s sc tr0 (its own prefix trace tr0), and derives a callee's peak premise from the
   entry's by pkR_app at the split of the granted trace. Both are state-free: the caller passes
   s := rs_live (room_of_cf S) and sc := rs_live (room_of_cf Sc), so this file needs no class.
   ================================================================================================ *)

(* the block's live requests are the entry's moved by the events of its prefix trace *)
Definition pi_live (s sc : list Z) (tr0 : list PjGrammar.ev) : Prop :=
  Permutation sc (PresetReqAt.hlive_from s (PresetReqAt.rd_hevs tr0)).

(* one event's step respects a permutation of the live list (rm1_perm / rmall) *)
Lemma pi_rmall_perm : forall F a b, Permutation a b -> Permutation (PresetReqAt.rmall F a) (PresetReqAt.rmall F b).
Proof.
intros F. unfold PresetReqAt.rmall. induction F as [|z F IH]; intros a b H; [exact H|].
cbn [fold_left]. apply IH. apply PresetReqAt.rm1_perm. exact H.
Qed.

Lemma pi_hstep_perm : forall e a b, Permutation a b ->
  Permutation (PresetReqAt.hstep a e) (PresetReqAt.hstep b e).
Proof.
intros [n|m n|n|L] a b H; cbn [PresetReqAt.hstep].
- apply perm_skip. exact H.
- apply perm_skip. apply PresetReqAt.rm1_perm. exact H.
- apply PresetReqAt.rm1_perm. exact H.
- apply pi_rmall_perm. exact H.
Qed.

Lemma pi_hlive_from_perm : forall es a b, Permutation a b ->
  Permutation (PresetReqAt.hlive_from a es) (PresetReqAt.hlive_from b es).
Proof.
induction es as [|e r IH]; intros a b H; [exact H|].
rewrite !PresetReqAt.hlive_from_cons. apply IH. apply pi_hstep_perm. exact H.
Qed.

(* at the entry: no event yet *)
Lemma pi_live_nil : forall s, pi_live s s [].
Proof. intros s. unfold pi_live. cbn [PresetReqAt.rd_hevs flat_map]. rewrite PresetReqAt.hlive_from_nil. apply Permutation_refl. Qed.

(* a step that does not change the live requests keeps it *)
Lemma pi_live_eq : forall s sc1 sc2 tr0, Permutation sc2 sc1 -> pi_live s sc1 tr0 -> pi_live s sc2 tr0.
Proof. intros s sc1 sc2 tr0 E H. unfold pi_live in *. exact (Permutation_trans E H). Qed.

(* an extension whose events are none keeps it *)
Lemma pi_live_noev : forall s sc tr0 t, PresetReqAt.rd_hevs t = [] -> pi_live s sc tr0 -> pi_live s sc (tr0 ++ t).
Proof.
intros s sc tr0 t Ht H. unfold pi_live in *.
rewrite PresetReqAt.rd_hevs_app, Ht, app_nil_r. exact H.
Qed.

(* a callee that moves the live requests by the events of its own trace extends it *)
Lemma pi_live_call : forall s sc sc' tr0 trc,
  pi_live s sc tr0 ->
  Permutation sc' (PresetReqAt.hlive_from sc (PresetReqAt.rd_hevs trc)) ->
  pi_live s sc' (tr0 ++ trc).
Proof.
intros s sc sc' tr0 trc H Hc. unfold pi_live in *.
rewrite PresetReqAt.rd_hevs_app, PresetReqAt.hlive_from_app.
exact (Permutation_trans Hc (pi_hlive_from_perm _ _ _ H)).
Qed.

(* ---- the counts. pi_lc f s Eg b is the entry premise's shape: the peak of f along the all-granted events Eg,
   from the entry's live requests s, is at most b ---- *)
Definition pi_lc (f : Z -> bool) (s : list Z) (Eg : list PresetReqAt.hev) (b : Z) : Prop :=
  Z.of_nat (PresetRun.pkR f s Eg) <= b.

(* the split: a callee whose all-granted events are the tail E2 of the entry's list, reached after E1, inherits the
   bound at the live requests E1 left (pkR_app) *)
Lemma pi_lc_tail : forall f s E1 E2 b, pi_lc f s (E1 ++ E2) b ->
  pi_lc f (PresetReqAt.hlive_from s E1) E2 b.
Proof.
intros f s E1 E2 b H. unfold pi_lc in *. rewrite PresetRun.pkR_app in H. lia.
Qed.

(* ... and the block's own live list is that one up to order (pi_live), which the count does not see *)
Lemma pi_lc_perm : forall f s s' E b, Permutation s' s -> pi_lc f s E b -> pi_lc f s' E b.
Proof.
intros f s s' E b Hp H. unfold pi_lc in *.
pose proof (PresetRun.pkR_mono f E s' s (PresetReqAt.subm_perm s' s (Permutation_sym Hp))) as Hm. lia.
Qed.

(* the two together, as a block uses them: from the entry bound over the whole granted list, at the block's state *)
Lemma pi_lc_at : forall f s sc tr0 E1 E2 b, pi_live s sc tr0 ->
  PresetReqAt.rd_hevs tr0 = E1 -> pi_lc f s (E1 ++ E2) b -> pi_lc f sc E2 b.
Proof.
intros f s sc tr0 E1 E2 b Hl HE H. unfold pi_live in Hl. rewrite HE in Hl.
exact (pi_lc_perm f _ _ E2 b Hl (pi_lc_tail f s E1 E2 b H)).
Qed.

(* ================================================================================================
   THE LIVE BYTES PER EVENT (the batch kit tip c23331281d07: rd_room's live conjunct and tgrow_specX's premise become
   rd_room's live conjunct and tgrow_specX's premise become PRH_Base.prh_live_evs S E := forall j e, nth_error E j = Some e ->
     fold_right Z.add 0 (hlive_from (rs_live (room_of_cf S)) (firstn j E)) + prh_ev_req e <= LIVE_MAX).
   Stated here over its unfolded body (s the live list, req the request of an event, b the bound), so it carries
   over any state: a callee's events are a PREFIX of the caller's, and after a prefix E1 the block's live list is the
   entry's moved by E1 (pi_live), which leaves the rest's per-event bound.
   ================================================================================================ *)
Definition pi_evs_ok (req : PresetReqAt.hev -> Z) (b : Z) (s : list Z) (E : list PresetReqAt.hev) : Prop :=
  forall (j : nat) (e : PresetReqAt.hev), nth_error E j = Some e ->
    fold_right Z.add 0 (PresetReqAt.hlive_from s (firstn j E)) + req e <= b.

Lemma pi_sum_perm : forall a b : list Z, Permutation a b -> fold_right Z.add 0 a = fold_right Z.add 0 b.
Proof. intros a b H. induction H; cbn [fold_right]; lia. Qed.

(* a prefix of the events keeps the bound *)
Lemma pi_evs_ok_pre : forall req b s E1 E2, pi_evs_ok req b s (E1 ++ E2) -> pi_evs_ok req b s E1.
Proof.
intros req b s E1 E2 H j e Hj. pose proof (proj1 (nth_error_Some E1 j) ltac:(rewrite Hj; discriminate)) as Hl.
assert (Hj' : nth_error (E1 ++ E2) j = Some e) by (rewrite nth_error_app1 by exact Hl; exact Hj).
specialize (H j e Hj'). rewrite firstn_app in H. replace (j - length E1)%nat with 0%nat in H by (clear - Hl; lia).
rewrite firstn_O, app_nil_r in H. exact H.
Qed.

(* after a prefix E1, at a live list that is the entry's moved by E1, the rest keeps the bound *)
Lemma pi_evs_ok_after : forall req b s s' E1 E2, pi_evs_ok req b s (E1 ++ E2) ->
  Permutation s' (PresetReqAt.hlive_from s E1) -> pi_evs_ok req b s' E2.
Proof.
intros req b s s' E1 E2 H Hp j e Hj.
assert (Hj' : nth_error (E1 ++ E2) (length E1 + j) = Some e).
{ rewrite nth_error_app2 by (clear; lia). replace (length E1 + j - length E1)%nat with j by (clear; lia). exact Hj. }
specialize (H _ e Hj'). rewrite firstn_app, firstn_all2 in H by (clear; lia).
replace (length E1 + j - length E1)%nat with j in H by (clear; lia).
rewrite PresetReqAt.hlive_from_app in H.
rewrite (pi_sum_perm _ _ (pi_hlive_from_perm (firstn j E2) _ _ Hp)). exact H.
Qed.

(* the two together, as a block uses them at a call: the callee's events E2 follow the prefix E1 in the granted run,
   and more events E3 may follow the callee's *)
Lemma pi_evs_ok_call : forall req b s s' E1 E2 E3, pi_evs_ok req b s (E1 ++ E2 ++ E3) ->
  Permutation s' (PresetReqAt.hlive_from s E1) -> pi_evs_ok req b s' E2.
Proof.
intros req b s s' E1 E2 E3 H Hp.
exact (pi_evs_ok_pre req b s' E2 E3 (pi_evs_ok_after req b s s' E1 (E2 ++ E3) H Hp)).
Qed.
