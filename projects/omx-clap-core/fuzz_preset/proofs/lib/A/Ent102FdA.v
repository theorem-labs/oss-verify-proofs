(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Ent102FdA.v, with its module paths changed; 15 of its 155 lines of code are new or changed. *)
(* omx-clap-core/fuzz_preset (both images; image-free): a document tree is freeable by pj_free to its depth. The kit's
   reader vocabulary (lib/A/PRH_Reader.v 91d2dbd40054: pj_nodeR, the tree at p; pj_fdR d, freeable by pj_free to
   depth d) has no lemma from the first to the second; the walk of LLVMFuzzerTestOneInput needs it at every path that
   reaches `pj_free (&doc)` with a TREE at &doc (the out_of_memory arms after parse_noting, check_as_written's r = 1,
   check_round_trip's r = 1, the `j` after check_reject_clean_starved (.., &doc)): the kit's tpj_free_specX takes pj_fdR at
   DOC_D = S MAXD, and a reading has depth <= MAXD (PjGrammar.json_read_depth). EntryCutsB's gap G17.
   rule 24: proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
Import ListNotations.
Local Open Scope Z_scope.

Section fd.
Variable segs : list Segment.
Variable m : word -> option byte.
Variable lblk : Z -> Z -> Prop.

Lemma ec_items_fd : forall d,
  (forall t p D, pj_nodeR segs m lblk p t D -> (depth t <= d)%nat -> pj_fdR segs m lblk d p D) ->
  forall items a ka Di,
  Forall (fun u => (depth u <= d)%nat) items ->
  pj_itemsR (pj_nodeR segs m lblk) a items Di ->
  pf_itemsR segs m lblk (pj_fdR segs m lblk d) false a ka (length items) Di.
Proof.
intros d IH items. induction items as [|u r IHr]; intros a ka Di HF HI; cbn [pj_itemsR pf_itemsR length] in *.
- exact HI.
- destruct HI as (D1 & D2 & -> & HP & HR). inversion HF as [|? ? Hu Hr]; subst.
  exists [], D1, D2. split; [reflexivity|]. split; [cbn [pj_keyR]; reflexivity|].
  split; [exact (IH u a D1 HP Hu)|]. exact (IHr (a + 56) (ka + 8) D2 Hr HR).
Qed.

Lemma ec_mems_fd : forall d,
  (forall t p D, pj_nodeR segs m lblk p t D -> (depth t <= d)%nat -> pj_fdR segs m lblk d p D) ->
  forall (members : list (list Z * jv)) a ka Di,
  Forall (fun mm => (depth (snd mm) <= d)%nat) members ->
  pj_memsR segs m lblk (pj_nodeR segs m lblk) a ka members Di ->
  pf_itemsR segs m lblk (pj_fdR segs m lblk d) true a ka (length members) Di.
Proof.
intros d IH members. induction members as [|[nm u] r IHr]; intros a ka Di HF HM; cbn [pj_memsR pf_itemsR length] in *.
- exact HM.
- destruct HM as (x & k & D1 & D2 & -> & Hx & Hs & HP & HR). inversion HF as [|? ? Hu Hr]; subst.
  exists [(x, k)], D1, D2. split; [reflexivity|].
  split; [cbn [pj_keyR]; exists x; split; [exact Hx | right; exists k; split; [exact (proj1 Hs) | reflexivity]]|].
  split; [exact (IH u a D1 HP Hu)|]. exact (IHr (a + 56) (ka + 8) D2 Hr HR).
Qed.

Lemma ec_depth_items : forall items d, (depth (JArr items) <= S d)%nat -> Forall (fun u => (depth u <= d)%nat) items.
Proof.
intros items d H. cbn [depth] in H. apply le_S_n in H. apply list_max_le in H.
apply Forall_map in H. exact H.
Qed.

Lemma ec_depth_members : forall members d, (depth (JObj members) <= S d)%nat ->
  Forall (fun mm : list Z * jv => (depth (snd mm) <= d)%nat) members.
Proof.
intros members d H. cbn [depth] in H. apply le_S_n in H. apply list_max_le in H.
apply Forall_map in H. eapply Forall_impl; [|exact H]. intros [nm v] Hv. exact Hv.
Qed.

(* the tree at p, of depth at most d, is freeable to depth d *)
Theorem ec_node_fd : forall d t p D, pj_nodeR segs m lblk p t D -> (depth t <= d)%nat -> pj_fdR segs m lblk d p D.
Proof.
induction d as [|d IH]; intros t p D H Hd;
  destruct t as [| | | txt bits | s | items | members]; cbn [depth] in Hd; try lia;
  cbn [pj_nodeR] in H; destruct H as (ND & AP & num & str & kids & keys & n & cap & HH & HC);
  cbn [pj_fdR]; unfold pj_fshapeR; split; try exact ND; split; try exact AP.
- destruct HC as (-> & -> & -> & -> & -> & ->).
  exists (tag JNull), num, 0, 0, 0, 0, 0, false, [], [], [], [].
  split; [exact HH|]. split; [left; split; reflexivity|]. split; [left; repeat split; reflexivity|].
  split; [left; repeat split; reflexivity|]. split; [apply Permutation_refl|]. split; reflexivity.
- destruct HC as (-> & -> & -> & -> & -> & ->).
  exists (tag JFalse), num, 0, 0, 0, 0, 0, false, [], [], [], [].
  split; [exact HH|]. split; [left; split; reflexivity|]. split; [left; repeat split; reflexivity|].
  split; [left; repeat split; reflexivity|]. split; [apply Permutation_refl|]. split; reflexivity.
- destruct HC as (-> & -> & -> & -> & -> & ->).
  exists (tag JTrue), num, 0, 0, 0, 0, 0, false, [], [], [], [].
  split; [exact HH|]. split; [left; split; reflexivity|]. split; [left; repeat split; reflexivity|].
  split; [left; repeat split; reflexivity|]. split; [apply Permutation_refl|]. split; reflexivity.
- destruct HC as (_ & -> & -> & -> & -> & k & Hs & ->).
  exists (tag (JNum txt bits)), num, str, 0, 0, 0, 0, false, [(str, k)], [], [], [].
  split; [exact HH|]. split; [right; exists k; split; [exact (proj1 Hs) | reflexivity]|].
  split; [left; repeat split; reflexivity|]. split; [left; repeat split; reflexivity|].
  split; [cbn; apply Permutation_refl|]. split; reflexivity.
- destruct HC as (-> & -> & -> & -> & k & Hs & ->).
  exists (tag (JStr s)), num, str, 0, 0, 0, 0, false, [(str, k)], [], [], [].
  split; [exact HH|]. split; [right; exists k; split; [exact (proj1 Hs) | reflexivity]|].
  split; [left; repeat split; reflexivity|]. split; [left; repeat split; reflexivity|].
  split; [cbn; apply Permutation_refl|]. split; reflexivity.
- destruct HC as (-> & -> & -> & -> & -> & ->).
  exists (tag JNull), num, 0, 0, 0, 0, 0, false, [], [], [], [].
  split; [exact HH|]. split; [left; split; reflexivity|]. split; [left; repeat split; reflexivity|].
  split; [left; repeat split; reflexivity|]. split; [apply Permutation_refl|]. reflexivity.
- destruct HC as (-> & -> & -> & -> & -> & ->).
  exists (tag JFalse), num, 0, 0, 0, 0, 0, false, [], [], [], [].
  split; [exact HH|]. split; [left; split; reflexivity|]. split; [left; repeat split; reflexivity|].
  split; [left; repeat split; reflexivity|]. split; [apply Permutation_refl|]. reflexivity.
- destruct HC as (-> & -> & -> & -> & -> & ->).
  exists (tag JTrue), num, 0, 0, 0, 0, 0, false, [], [], [], [].
  split; [exact HH|]. split; [left; split; reflexivity|]. split; [left; repeat split; reflexivity|].
  split; [left; repeat split; reflexivity|]. split; [apply Permutation_refl|]. reflexivity.
- destruct HC as (_ & -> & -> & -> & -> & k & Hs & ->).
  exists (tag (JNum txt bits)), num, str, 0, 0, 0, 0, false, [(str, k)], [], [], [].
  split; [exact HH|]. split; [right; exists k; split; [exact (proj1 Hs) | reflexivity]|].
  split; [left; repeat split; reflexivity|]. split; [left; repeat split; reflexivity|].
  split; [cbn; apply Permutation_refl|]. reflexivity.
- destruct HC as (-> & -> & -> & -> & k & Hs & ->).
  exists (tag (JStr s)), num, str, 0, 0, 0, 0, false, [(str, k)], [], [], [].
  split; [exact HH|]. split; [right; exists k; split; [exact (proj1 Hs) | reflexivity]|].
  split; [left; repeat split; reflexivity|]. split; [left; repeat split; reflexivity|].
  split; [cbn; apply Permutation_refl|]. reflexivity.
- destruct HC as (-> & -> & Hn & Hncap & Hcap & Di & -> & HI).
  pose proof (ec_depth_items items d Hd) as HF.
  destruct Hcap as [(-> & ->) | (Hc0 & Hk)].
  + assert (Hl : length items = 0%nat) by lia.
    exists (tag (JArr items)), num, 0, 0, 0, n, 0, false, [], [], [], Di.
    split; [exact HH|]. split; [left; split; reflexivity|]. split; [left; split; [reflexivity | split; [lia | reflexivity]]|].
    split; [left; repeat split; reflexivity|]. split; [cbn; apply Permutation_refl|].
    rewrite Hn, Nat2Z.id. exact (ec_items_fd d IH items 0 0 Di HF HI).
  + assert (E : (cap =? 0) = false) by (apply Z.eqb_neq; lia). rewrite E.
    exists (tag (JArr items)), num, 0, kids, 0, n, cap, false, [], [(kids, 56 * cap)], [], Di.
    split; [exact HH|]. split; [left; split; reflexivity|].
    split; [right; exists (56 * cap); split; [exact Hk | split; [lia | reflexivity]]|].
    split; [left; repeat split; reflexivity|]. split; [cbn; apply Permutation_refl|].
    rewrite Hn, Nat2Z.id. exact (ec_items_fd d IH items kids 0 Di HF HI).
- destruct HC as (-> & Hn & Hncap & Hcap & Di & -> & HM).
  pose proof (ec_depth_members members d Hd) as HF.
  destruct Hcap as [(-> & -> & ->) | (Hc0 & Hk & Hy)].
  + assert (Hl : length members = 0%nat) by lia.
    destruct members as [|mm r]; [|cbn in Hl; discriminate].
    cbn [pj_memsR] in HM. subst Di. cbn [length] in Hn. change (Z.of_nat 0) with 0 in Hn. subst n.
    exists (tag (JObj [])), num, 0, 0, 0, 0, 0, false, [], [], [], [].
    split; [exact HH|]. split; [left; split; reflexivity|]. split; [left; repeat split; reflexivity|].
    split; [left; repeat split; reflexivity|]. split; [cbn; apply Permutation_refl|]. reflexivity.
  + assert (E : (cap =? 0) = false) by (apply Z.eqb_neq; lia). rewrite E.
    exists (tag (JObj members)), num, 0, kids, keys, n, cap, true, [], [(kids, 56 * cap)], [(keys, 8 * cap)], Di.
    split; [exact HH|]. split; [left; split; reflexivity|].
    split; [right; exists (56 * cap); split; [exact Hk | split; [lia | reflexivity]]|].
    split; [right; split; [reflexivity | exists (8 * cap); split; [exact Hy | split; [lia | reflexivity]]]|].
    split; [cbn; apply Permutation_refl|].
    rewrite Hn, Nat2Z.id. exact (ec_mems_fd d IH members kids keys Di HF HM).
Qed.

End fd.

(* at the free cut: a reading's tree is freeable to DOC_D *)
Corollary ec_read_fd : forall segs m lblk x t p D,
  json_read ReaderRes.jr_strtod x = Some t -> pj_nodeR segs m lblk p t D -> pj_fdR segs m lblk PRH_Base.DOC_D p D.
Proof.
intros segs m lblk x t p D Hr Hn. apply (ec_node_fd segs m lblk PRH_Base.DOC_D t p D Hn).
pose proof (json_read_depth ReaderRes.jr_strtod x t Hr). unfold PRH_Base.DOC_D. lia.
Qed.

(* the same at a REFUSED run: cut_pno / cut_caw carry `jr_run (e_x E) ok = (Some t, tr)`, not ck_read, and their
   FREE arms (out_of_memory after parse_noting; check_as_written's r = 1) must pay cut_free's pj_fdR too. The depth
   bound holds for ANY ok list: PjGrammar.jr_value_depth is quantified over it, and jr_run reads jr_value 0. *)
Lemma ec_run_depth : forall sm x ok t tr, PjGrammar.jr_run sm x ok = (Some t, tr) -> (depth t <= MAXD)%nat.
Proof.
intros sm x ok t tr H. unfold PjGrammar.jr_run in H.
destruct (PjGrammar.jr_value sm 0 x ok) as [[[[t' r]|] tr'] ok'] eqn:E; [|injection H as H _; discriminate].
pose proof (PjGrammar.jr_value_depth sm 0 x ok t' r tr' ok' E) as Hd.
destruct (PjGrammar.skip r) as [|c z]; injection H as Ht _; [|discriminate].
subst t'. rewrite Nat.sub_0_r in Hd. exact Hd.
Qed.

Corollary ec_run_fd : forall segs m lblk sm x ok t tr p D,
  PjGrammar.jr_run sm x ok = (Some t, tr) -> pj_nodeR segs m lblk p t D -> pj_fdR segs m lblk PRH_Base.DOC_D p D.
Proof.
intros segs m lblk sm x ok t tr p D Hr Hn. apply (ec_node_fd segs m lblk PRH_Base.DOC_D t p D Hn).
pose proof (ec_run_depth sm x ok t tr Hr). unfold PRH_Base.DOC_D. lia.
Qed.

Print Assumptions ec_read_fd.
Print Assumptions ec_run_fd.
