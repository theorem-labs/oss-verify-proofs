(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, the tree facts of PRH_Reader's restated predicates, IMAGE-FREE (no image
   instance, no Require of an image file): a represented tree is freeable to its depth (pjg_node_fd), and freeable is
   monotone in the depth (pjg_fd_succ, pjg_fd_mono), with the item / member lemmas they use. Transcribed from preset's
   plain lib/Prog/PjStruct.v:412-572 (pf_items_mono, pj_fshape_mono, pj_fd_succ, pj_fd_mono, pj_items_pf, pj_mems_pf,
   pj_node_fd) over lib/A/PRH_Reader.v's predicates; no plain lemma is cited. Moved verbatim from module PjpTree of
   lib/B/Prog/pj_parse_glue.v (cold/h-rw-pre-7-b-pj_parse 175b3601c4e6, :44-196), so that other walks (pj_set) can
   Require it without pj_parse's image-B files. Names are unchanged: PjpTree.pjg_fd_mono, PjpTree.pjg_node_fd, ...
   rule 24: proves no function (kind: glue lemma). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import PjTree.
Section tree.
Variable segs : list Segment.

Lemma pjg_pf_mono : forall m lblk (P Q : Z -> list (Z * Z) -> Prop) ks n a ka D,
  (forall a D1, P a D1 -> Q a D1) -> pf_itemsR segs m lblk P ks a ka n D -> pf_itemsR segs m lblk Q ks a ka n D.
Proof.
  intros m lblk P Q ks n. induction n as [|n IH]; intros a ka D H Hp; cbn [pf_itemsR] in *.
  - exact Hp.
  - destruct Hp as (Dk & D1 & D2 & E & Hk & HP & HR). exists Dk, D1, D2.
    split; [exact E|]. split; [exact Hk|]. split; [exact (H a D1 HP) | exact (IH (a + 56) (ka + 8) D2 H HR)].
Qed.

Lemma pjg_fshape_mono : forall m lblk (Pi Pi' : bool -> Z -> Z -> Z -> list (Z * Z) -> Prop) p D,
  (forall ks kids keys n Di, Pi ks kids keys n Di -> Pi' ks kids keys n Di) ->
  pj_fshapeR segs m lblk Pi p D -> pj_fshapeR segs m lblk Pi' p D.
Proof.
  intros m lblk Pi Pi' p D H
    (Hn & Ha & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & H1 & H2 & H3 & H4 & H5 & H6).
  split; [exact Hn|]. split; [exact Ha|]. exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  exact (H _ _ _ _ _ H6).
Qed.

Lemma pjg_fd_succ : forall m lblk d p D, pj_fdR segs m lblk d p D -> pj_fdR segs m lblk (S d) p D.
Proof.
  intros m lblk d. induction d as [|d IH]; intros p D H; cbn [pj_fdR] in H |- *.
  - eapply (pjg_fshape_mono m lblk); [|exact H].
    intros ks kids keys n Di (En & EDi). cbv beta. subst n Di. exact eq_refl.
  - eapply (pjg_fshape_mono m lblk); [|exact H].
    intros ks kids keys n Di Hi. cbv beta in Hi |- *.
    apply (pjg_pf_mono m lblk (pj_fdR segs m lblk d)); [|exact Hi].
    intros a D1 H1. exact (IH a D1 H1).
Qed.

Lemma pjg_fd_mono : forall m lblk d d' p D, (d <= d')%nat -> pj_fdR segs m lblk d p D -> pj_fdR segs m lblk d' p D.
Proof.
  intros m lblk d d' p D Hle. induction Hle as [|d' Hle IH]; intros H; [exact H|].
  apply pjg_fd_succ. apply IH. exact H.
Qed.

Lemma pjg_items_pf : forall m lblk (P : Z -> jv -> list (Z * Z) -> Prop) (Q : Z -> list (Z * Z) -> Prop) l a ka D,
  (forall a u D1, In u l -> P a u D1 -> Q a D1) ->
  pj_itemsR P a l D -> pf_itemsR segs m lblk Q false a ka (length l) D.
Proof.
  intros m lblk P Q l. induction l as [|u r IH]; intros a ka D H Hl; cbn [pj_itemsR pf_itemsR length] in *.
  - exact Hl.
  - destruct Hl as (D1 & D2 & E & HP & HR). exists [], D1, D2.
    split; [exact E|]. split; [exact eq_refl|]. split; [apply (H a u D1); [left; reflexivity | exact HP]|].
    apply IH; [intros a' v D3 Hv HP3; apply (H a' v D3); [right; exact Hv | exact HP3] | exact HR].
Qed.

Lemma pjg_mems_pf : forall m lblk (P : Z -> jv -> list (Z * Z) -> Prop) (Q : Z -> list (Z * Z) -> Prop) l a ka D,
  (forall a u D1, (exists nm, In (nm, u) l) -> P a u D1 -> Q a D1) ->
  pj_memsR segs m lblk P a ka l D -> pf_itemsR segs m lblk Q true a ka (length l) D.
Proof.
  intros m lblk P Q l. induction l as [|[nm u] r IH]; intros a ka D H Hl; cbn [pj_memsR pf_itemsR length] in *.
  - exact Hl.
  - destruct Hl as (x & k & D1 & D2 & E & Hx & (Hb & _) & HP & HR). exists [(x, k)], D1, D2.
    split; [exact E|].
    split; [unfold pj_keyR; exists x; split; [exact Hx | right; exists k; split; [exact Hb | reflexivity]]|].
    split; [apply (H a u D1); [exists nm; left; reflexivity | exact HP]|].
    apply IH; [intros a' v D3 (nm' & Hv) HP3; apply (H a' v D3); [exists nm'; right; exact Hv | exact HP3] | exact HR].
Qed.

Lemma pjg_node_fd : forall t m lblk p D, pj_nodeR segs m lblk p t D -> pj_fdR segs m lblk (depth t) p D.
Proof.
  intros t. induction t as [| | | txt bits | s | items IH | members IH] using jv_ind'; intros m lblk p D H;
    cbn [pj_nodeR] in H.
  - destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & ED).
    cbn [depth pj_fdR]. unfold pj_fshapeR. split; [exact Hn|]. split; [exact Ha|].
    exists (tag JNull), num, str, kids, keys, n, cap, false, [], [], [], [].
    split; [exact Hh|]. split; [left; split; [exact E1 | reflexivity]|].
    split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
    split; [left; split; [exact E3 | split; reflexivity]|].
    split; [subst D; apply Permutation_refl|]. split; [exact E4 | reflexivity].
  - destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & ED).
    cbn [depth pj_fdR]. unfold pj_fshapeR. split; [exact Hn|]. split; [exact Ha|].
    exists (tag JFalse), num, str, kids, keys, n, cap, false, [], [], [], [].
    split; [exact Hh|]. split; [left; split; [exact E1 | reflexivity]|].
    split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
    split; [left; split; [exact E3 | split; reflexivity]|].
    split; [subst D; apply Permutation_refl|]. split; [exact E4 | reflexivity].
  - destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & ED).
    cbn [depth pj_fdR]. unfold pj_fshapeR. split; [exact Hn|]. split; [exact Ha|].
    exists (tag JTrue), num, str, kids, keys, n, cap, false, [], [], [], [].
    split; [exact Hh|]. split; [left; split; [exact E1 | reflexivity]|].
    split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
    split; [left; split; [exact E3 | split; reflexivity]|].
    split; [subst D; apply Permutation_refl|]. split; [exact E4 | reflexivity].
  - destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & k & (Hb & _) & ED).
    cbn [depth pj_fdR]. unfold pj_fshapeR. split; [exact Hn|]. split; [exact Ha|].
    exists (tag (JNum txt bits)), num, str, kids, keys, n, cap, false, [(str, k)], [], [], [].
    split; [exact Hh|]. split; [right; exists k; split; [exact Hb | reflexivity]|].
    split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
    split; [left; split; [exact E3 | split; reflexivity]|].
    split; [subst D; cbn [app]; apply Permutation_refl|]. split; [exact E4 | reflexivity].
  - destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E2 & E3 & E4 & E5 & k & (Hb & _) & ED).
    cbn [depth pj_fdR]. unfold pj_fshapeR. split; [exact Hn|]. split; [exact Ha|].
    exists (tag (JStr s)), num, str, kids, keys, n, cap, false, [(str, k)], [], [], [].
    split; [exact Hh|]. split; [right; exists k; split; [exact Hb | reflexivity]|].
    split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
    split; [left; split; [exact E3 | split; reflexivity]|].
    split; [subst D; cbn [app]; apply Permutation_refl|]. split; [exact E4 | reflexivity].
  - destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Es & Ek & En & Hc & Hcap & Di & ED & Hi).
    remember (depth (JArr items)) as dd eqn:Edd. destruct dd as [|d']; [cbn [depth] in Edd; discriminate|].
    cbn [pj_fdR]. unfold pj_fshapeR.
    split; [exact Hn|]. split; [exact Ha|].
    assert (HI : pf_itemsR segs m lblk (pj_fdR segs m lblk d') false kids keys (Z.to_nat n) Di).
    { rewrite En, Nat2Z.id. apply (pjg_items_pf m lblk (pj_nodeR segs m lblk)); [|exact Hi].
      intros a u D1 Hu HP. rewrite Forall_forall in IH.
      apply (pjg_fd_mono m lblk (depth u)); [|exact (IH u Hu m lblk a D1 HP)].
      pose proof (depth_item items u Hu). lia. }
    destruct Hcap as [(Hc0 & Hk0)|(Hc0 & Hl)].
    + subst cap.
      exists (tag (JArr items)), num, str, kids, keys, n, 0, false, [], [], [], Di.
      split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
      split; [left; split; [exact Hk0 | split; [lia | reflexivity]]|].
      split; [left; split; [exact Ek | split; reflexivity]|].
      split; [subst D; cbn; apply Permutation_refl|]. exact HI.
    + rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia.
      exists (tag (JArr items)), num, str, kids, keys, n, cap, false, [], [(kids, 56 * cap)], [], Di.
      split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
      split; [right; exists (56 * cap); split; [exact Hl | split; [lia | reflexivity]]|].
      split; [left; split; [exact Ek | split; reflexivity]|].
      split; [subst D; cbn [app]; apply Permutation_refl|]. exact HI.
  - destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Es & En & Hc & Hcap & Di & ED & Hi).
    remember (depth (JObj members)) as dd eqn:Edd. destruct dd as [|d']; [cbn [depth] in Edd; discriminate|].
    cbn [pj_fdR]. unfold pj_fshapeR.
    split; [exact Hn|]. split; [exact Ha|].
    destruct Hcap as [(Hc0 & Hk0 & Hy0)|(Hc0 & L0 & L1)].
    + subst cap. destruct members as [|mb members]; cbn [length] in En; [|lia].
      cbn [pj_memsR] in Hi.
      exists (tag (JObj [])), num, str, kids, keys, n, 0, false, [], [], [], Di.
      split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
      split; [left; split; [exact Hk0 | split; [lia | reflexivity]]|].
      split; [left; split; [exact Hy0 | split; reflexivity]|].
      split; [subst D; cbn; apply Permutation_refl|].
      cbv beta. replace (Z.to_nat n) with 0%nat by lia. exact Hi.
    + rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia.
      exists (tag (JObj members)), num, str, kids, keys, n, cap, true, [], [(kids, 56 * cap)], [(keys, 8 * cap)], Di.
      split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
      split; [right; exists (56 * cap); split; [exact L0 | split; [lia | reflexivity]]|].
      split; [right; split; [reflexivity | exists (8 * cap); split; [exact L1 | split; [lia | reflexivity]]]|].
      split; [subst D; cbn [app]; apply Permutation_refl|].
      cbv beta. rewrite En, Nat2Z.id. apply (pjg_mems_pf m lblk (pj_nodeR segs m lblk)); [|exact Hi].
      intros a u D1 (nm & Hu) HP. rewrite Forall_forall in IH. specialize (IH (nm, u) Hu). cbn [snd] in IH.
      apply (pjg_fd_mono m lblk (depth u)); [|exact (IH m lblk a D1 HP)].
      pose proof (depth_member members nm u Hu). lia.
Qed.
End tree.
