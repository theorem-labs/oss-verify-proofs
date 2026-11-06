(* Theorem Labs, 2026-10: THE BATCH KIT'S LEDGER MOVE across a prefix and a call (lane PItemsB, owner; a Theorem Labs lane's order, item 4).
   The batch kit (a working branch 8ba304fe2f93, lib/A/PRH_FnParse.v 4fe5b038ae41:173-182) prices a
   refusal: rd_ledger_move takes g_most and the call's ALL-GRANTED trace gt, keys g_ran_out on each call's request
   against g_most (PRH_Base.prh_oks, :841-845) and adds prh_refused_peak over prh_ev_helds gt (:854-873).
   parse_items' walk reaches every block of its loop only while every allocation so far was GRANTED, so its prefix
   move is over gt := its own trace and refusal-free (PItems_defs.v pi_led); at an exit the prefix composes with the
   one call that ends the run. This file proves that composition and the list facts it needs. Pure trace / ledger
   algebra: no image fact, no numeral that names an address.
   Rule 24: proves no function (kind: shared lemma). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnParse.
From stdpp Require list_basics.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PItems_posb.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- prh_ev_helds over an append: the second part's helds are shifted by the first part's held bytes ---- *)
Lemma pik1_map_add_comp : forall (a b : Z) (l : list Z), map (Z.add a) (map (Z.add b) l) = map (Z.add (a + b)) l.
Proof. intros a b l. rewrite map_map. apply map_ext. intros x. lia. Qed.

Lemma pik1_helds_app : forall t1 t2,
  prh_ev_helds (t1 ++ t2) = prh_ev_helds t1 ++ map (Z.add (PjGrammar.held t1)) (prh_ev_helds t2).
Proof.
induction t1 as [|e r IH]; intros t2.
- cbn [app prh_ev_helds PjGrammar.held]. rewrite map_ext with (g := fun x => x) by (intros; lia). rewrite map_id.
  reflexivity.
- cbn [app prh_ev_helds PjGrammar.held]. rewrite IH, map_app, pik1_map_add_comp, app_assoc. reflexivity.
Qed.

Lemma pik1_helds_len : forall t, length (prh_ev_helds t) = PjGrammar.calls t.
Proof.
induction t as [|e r IH]; [reflexivity|]. cbn [prh_ev_helds PjGrammar.calls].
rewrite length_app, length_map, IH. destruct (PjGrammar.is_call e); reflexivity.
Qed.

(* prh_ev_reqs filters with stdpp's base.filter: its append law is stdpp.list_basics.list.filter_app *)
Lemma pik1_reqs_app : forall t1 t2, prh_ev_reqs (t1 ++ t2) = prh_ev_reqs t1 ++ prh_ev_reqs t2.
Proof. intros t1 t2. unfold prh_ev_reqs. rewrite list_basics.list.filter_app, List.map_app. reflexivity. Qed.

Lemma pik1_reqs_len : forall t, length (prh_ev_reqs t) = PjGrammar.calls t.
Proof.
intros t. unfold prh_ev_reqs. rewrite length_map. induction t as [|e r IH]; [reflexivity|].
change (e :: r) with ([e] ++ r). rewrite list_basics.list.filter_app, length_app, IH. cbn [app PjGrammar.calls].
destruct (PjGrammar.is_call e) eqn:E; [rewrite list_basics.list.filter_cons_True | rewrite list_basics.list.filter_cons_False];
  rewrite ?E; cbn; try reflexivity; try (intros H; exact H); try (intros H; exact (H I)).
Qed.

Lemma pik1_calls_app : forall t1 t2, PjGrammar.calls (t1 ++ t2) = (PjGrammar.calls t1 + PjGrammar.calls t2)%nat.
Proof.
induction t1 as [|e r IH]; intros t2; [reflexivity|]. cbn [app PjGrammar.calls].
rewrite IH. destruct (PjGrammar.is_call e); lia.
Qed.

Lemma pik1_held_app : forall t1 t2, PjGrammar.held (t1 ++ t2) = PjGrammar.held t1 + PjGrammar.held t2.
Proof. induction t1 as [|e r IH]; intros t2; cbn [app PjGrammar.held]; [lia | rewrite IH; lia]. Qed.

(* ---- the refusal predicate and the refusal peak over an outcome list ok1 ++ ok2, the first k1 calls granted ---- *)
Lemma pik1_refused_shift : forall ok1 ok2 cnt fail (k1 j : nat), length ok1 = k1 ->
  prh_refused (ok1 ++ ok2) cnt fail (k1 + j) = prh_refused ok2 (cnt + Z.of_nat k1) fail j.
Proof.
intros ok1 ok2 cnt fail k1 j Hl. unfold prh_refused.
rewrite app_nth2 by lia. replace (k1 + j - length ok1)%nat with j by lia.
replace (cnt + Z.of_nat (k1 + j)) with (cnt + Z.of_nat k1 + Z.of_nat j) by lia. reflexivity.
Qed.

Lemma pik1_refused_pre : forall ok1 ok2 cnt fail (k1 i : nat), length ok1 = k1 -> (i < k1)%nat ->
  prh_granted ok1 cnt fail k1 -> prh_refused (ok1 ++ ok2) cnt fail i = false.
Proof.
intros ok1 ok2 cnt fail k1 i Hl Hi G. unfold prh_refused. rewrite app_nth1 by lia.
destruct (nth i ok1 true) eqn:E; [reflexivity|].
rewrite (proj2 (Z.eqb_eq _ _) (G i Hi E)). reflexivity.
Qed.

Lemma pik1_fold_max_nonneg : forall l : list Z, 0 <= fold_right Z.max 0 l.
Proof. induction l as [|x r IH]; cbn [fold_right]; lia. Qed.

(* fold_right Z.max over an append is the max of the two halves *)
Lemma pik1_fold_max_app : forall (l1 l2 : list Z),
  fold_right Z.max 0 (l1 ++ l2) = Z.max (fold_right Z.max 0 l1) (fold_right Z.max 0 l2).
Proof.
induction l1 as [|x r IH]; intros l2; cbn [app fold_right].
- pose proof (pik1_fold_max_nonneg l2) as H. lia.
- rewrite IH. lia.
Qed.


(* ---- THE BATCH KIT LEDGER MOVE ACROSS A GRANTED PREFIX AND ONE CALL. The prefix is over its own trace (gt := tr1) and made
   no refusal (prh_granted); the call's move is over its own all-granted trace gt2, of which its actual trace makes
   at most as many calls. The whole move is over tr1 ++ gt2 ++ rest for ANY rest: the refusal peak reads only the
   first calls (tr1 ++ tr2) of it. ---- *)
Lemma pik1_seq_shift : forall (k s : nat), List.seq s k = map (Nat.add s) (List.seq 0 k).
Proof.
induction k as [|k IH]; intros s; [reflexivity|]. cbn [List.seq map]. rewrite Nat.add_0_r. f_equal.
rewrite (IH (S s)), (IH 1%nat), map_map. apply map_ext. intros a. lia.
Qed.

Lemma pik1_seq_split : forall (k1 k2 : nat), List.seq 0 (k1 + k2) = List.seq 0 k1 ++ map (Nat.add k1) (List.seq 0 k2).
Proof. intros k1 k2. rewrite List.seq_app, Nat.add_0_l, (pik1_seq_shift k2 k1). reflexivity. Qed.

(* a GRANTED move does not depend on the granted trace it is priced over (its refusal peak is 0 at any gt) *)
Lemma pik1_move_regt : forall Lam peak cnt fail ran most ok gt gt' tr D Lam' peak' cnt' fail' ran',
  prh_granted ok cnt fail (PjGrammar.calls tr) ->
  rd_ledger_move Lam peak cnt fail ran most ok gt tr D Lam' peak' cnt' fail' ran' ->
  rd_ledger_move Lam peak cnt fail ran most ok gt' tr D Lam' peak' cnt' fail' ran'.
Proof.
intros Lam peak cnt fail ran most ok gt gt' tr D Lam' peak' cnt' fail' ran' G (H1 & H2 & H3 & H4 & H5 & H6 & H7).
unfold rd_ledger_move. rewrite (prh_refused_peak_granted ok cnt fail _ _ G) in H7.
rewrite (prh_refused_peak_granted ok cnt fail _ _ G).
exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 H7)))))).
Qed.

(* a free event is not a harness call: it adds no request *)
Lemma pik1_reqs_free : forall t k, prh_ev_reqs (t ++ [PjGrammar.EFree k]) = prh_ev_reqs t.
Proof. intros t k. rewrite pik1_reqs_app, app_nil_r. reflexivity. Qed.

(* ---- THE GRANTED PREFIX (pi_grant) and the all-granted run: the OUTCOME's tools ---- *)
Lemma pik1_ok_upto_repeat : forall k j, PjGrammar.ok_upto (repeat true k) j.
Proof.
intros k j i _. revert i. induction k as [|k IH]; intros [|i]; cbn [repeat nth]; try reflexivity. apply IH.
Qed.

(* a run fed only grants equals the all-granted run (PjGrammar.agrees): same result, same trace *)
Lemma pik1_run_granted : forall (A : Type) (m : PjGrammar.M A) (k : nat) r t ok',
  PjGrammar.agrees m -> m (repeat true k) = (r, t, ok') -> fst (m []) = (r, t).
Proof.
intros A m k r t ok' H E.
pose proof (proj1 (H (repeat true k)) (pik1_ok_upto_repeat k _)) as E2. rewrite E in E2.
injection E2 as E3 E4 _. rewrite (surjective_pairing (fst (m []))). rewrite <- E3, <- E4. reflexivity.
Qed.

(* ... and when the grants are followed by more of the oracle that the run does not read *)
Lemma pik1_run_granted_app : forall (A : Type) (m : PjGrammar.M A) (k : nat) ok1 r t ok',
  PjGrammar.agrees m -> m (repeat true k ++ ok1) = (r, t, ok') -> PjGrammar.calls t = k -> fst (m []) = (r, t).
Proof.
intros A m k ok1 r t ok' H E Hc.
destruct (PjGrammar.ok_upto_dec (repeat true k ++ ok1) (PjGrammar.calls (snd (fst (m []))))) as [Hu|(j & Hj & Hf & Hu)].
- pose proof (proj1 (H _) Hu) as E2. rewrite E in E2. injection E2 as E3 E4 _.
  rewrite (surjective_pairing (fst (m []))). rewrite <- E3, <- E4. reflexivity.
- destruct (proj2 (H _) j Hj Hf Hu) as (P & e & rest & E2 & Et & HcP & Hce). rewrite E in E2.
  injection E2 as _ E4 _. subst t. rewrite PjGrammar.calls_app in Hc. cbn [PjGrammar.calls PjGrammar.is_call] in Hc.
  (* j = calls P < k: the j-th oracle bit is a grant *)
  assert (Hjk : (j < k)%nat) by lia.
  rewrite app_nth1 in Hf by (rewrite repeat_length; exact Hjk).
  assert (nth j (repeat true k) true = true) by exact (pik1_ok_upto_repeat k (S j) j ltac:(lia)). congruence.
Qed.

(* a granted prefix makes no refusal: prh_granted, and the ledger keeps g_ran_out *)
Lemma pik1_grant_granted : forall k cnt fail n, prh_granted (repeat true k) cnt fail n.
Proof. intros k cnt fail n i _ E. rewrite (pik1_ok_upto_repeat k (S i) i ltac:(lia)) in E. discriminate. Qed.

Lemma pik1_move_ran : forall Lam peak cnt fail ran most ok gt tr D Lam' peak' cnt' fail' ran',
  prh_granted ok cnt fail (PjGrammar.calls tr) ->
  rd_ledger_move Lam peak cnt fail ran most ok gt tr D Lam' peak' cnt' fail' ran' -> ran' = ran.
Proof.
intros Lam peak cnt fail ran most ok gt tr D Lam' peak' cnt' fail' ran' G ((_ & O & _) & _).
destruct O as [E | (_ & i & Hi & Hr & _)]; [exact E|].
unfold prh_refused in Hr. destruct (nth i ok true) eqn:Eb; [discriminate|].
rewrite (proj2 (Z.eqb_eq _ _) (G i Hi Eb)) in Hr. discriminate.
Qed.

(* ---- THE LIVE BYTES PER EVENT at a state (the batch kit's tip 03fcabb582d0: rd_room's live conjunct, tgrow_specX's and
   tparse_string_specX's live premises are PRH_Base.prh_live_evs S E): the prefix and after-prefix forms of
   PItems_posb.pi_evs_ok at the live list of a state. A call at the block state Sc, whose live list is the entry's
   moved by the prefix's events E1 (pi_live), gets its own events' bound E2 from the entry's over E1 ++ E2 ++ E3 ---- *)
Lemma pik1_live_evs_after : forall S Sc E1 E2, prh_live_evs S (E1 ++ E2) ->
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc)) (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) E1) ->
  prh_live_evs Sc E2.
Proof. intros S Sc E1 E2 H Hp. exact (PItems_posb.pi_evs_ok_after _ _ _ _ E1 E2 H Hp). Qed.

Lemma pik1_live_evs_pre : forall S E1 E2, prh_live_evs S (E1 ++ E2) -> prh_live_evs S E1.
Proof. intros S E1 E2 H. exact (PItems_posb.pi_evs_ok_pre _ _ _ E1 E2 H). Qed.

Lemma pik1_live_evs_call : forall S Sc E1 E2 E3, prh_live_evs S (E1 ++ E2 ++ E3) ->
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc)) (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) E1) ->
  prh_live_evs Sc E2.
Proof. intros S Sc E1 E2 E3 H Hp. exact (PItems_posb.pi_evs_ok_call _ _ _ _ E1 E2 E3 H Hp). Qed.

(* the same with pi_live's own statement (PItems_posb.pi_live s sc tr0 := Permutation sc (hlive_from s (rd_hevs tr0))) *)
Lemma pik1_live_evs_live : forall S Sc tr0 E2, prh_live_evs S (PresetReqAt.rd_hevs tr0 ++ E2) ->
  PItems_posb.pi_live (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc)) tr0 ->
  prh_live_evs Sc E2.
Proof. intros S Sc tr0 E2 H Hl. unfold PItems_posb.pi_live in Hl. exact (pik1_live_evs_after S Sc _ E2 H Hl). Qed.
