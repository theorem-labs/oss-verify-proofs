(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PItems_shape.v; 346 of its 430 lines of code are new or changed and 1233 lines of the source are left out. *)
(* Theorem Labs, 2026-10: THE FREE ORDER at parse_items' exits (lane PItemsB of a Theorem Labs lane's image-B walk, the batch kit
   240b06ed4fd4). PItems_shape.v proves at every exit the UNORDERED freeable shape pj_fdR (pis_exit_open,
   pis_exit_grow_kept, pis_exit_grow_half, pis_exit_item); the batch kit's post (lib/A/PRH_FnParse.v tparse_items_specX) states
   the ORDERED one, the kit's PRH_PjOrder.pj_foR, whose list F is pj_free's order (src/preset_file.c:334-350): for each slot
   the subtree of kids[i], then keys[i]; then kids, keys, str. This file gives the ordered twins, over `segs` as
   PItems_shape.v states its lemmas:
   - pis_fo_open / pis_fo_grow_kept / pis_fo_grow_half / pis_fo_item / pis_fo_close: the exit lemmas and pis_close,
     with the completed slots' order list Facc (pi_forder's pf_oitemsR, the kit's PRH_PjOrder.pf_oitemsR) in place of the
     depth bound of the items; each concludes pj_foR at depth S nn with F = <the slots' order list> ++ <the node's
     arrays, kids then keys> (str = 0 in a container). Each drops the unordered lemma's `d < MAXD` and
     `Forall (depth <= MAXD - S d) ts` (the order list carries the depth); pis_fo_grow_half also drops `0 <= k'` and
     `k' + 56 * len <= 2 ^ 64`, which no step of the ordered proof uses. Dropping a premise STRENGTHENS the lemma.
   - pis_fo_snoc: one more completed slot (its subtree's list, then its key) on the order list.
   - pis_fo_slots_hb / pis_fo_slots_hb_nat / pis_fo_kept_hb / pis_fo_half_hb: the arrays' requests against the kit's model
     (PresetReqAt.arrz, and PresetReqAt.gheld at a refused grow), stated at any head hd = PresetReqAt.HEAD.
   - pi_forder_post / pi_forder_at / pi_forder_close (pi_forder_mk): PItems_defs.pi_forder, stated at every nn that
     bounds the members' depths, at the post's depth n = S nn: a refusal exit's n >= MAXD - d (the members at most
     MAXD - S d deep), and the closer's n >= depth (mk o (rev acc)).
   Helpers: pis_fo_apart, pis_fo_node_xfer (a pj_foR node moved to a new address, the twin of pis_node_xfer),
   pis_fo_items_xfer (an order list moved with its slot arrays, the twin of pis_items_xfer), pis_fo_snoc_gen,
   pis_fo_shape (the node of an open container from its parts).
   Proves no function (kind: shared lemma of an existing walk; parse_items' top theorem is lane PItemsB's).
   Numerals: 56 / 8 the node and key-slot sizes (LENGTH), 5 / 6 the node types (TAG); no address. No Admitted, Axiom,
   Parameter or sorry. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP09 YI04 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfNames YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_Base PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PItems_shape.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PItems_defs.
Import ListNotations.
Local Open Scope Z_scope.

Section fo.
Variable segs : list Segment.

Lemma pis_fo_apart : forall m lblk d p D F, pj_foR segs m lblk d p D F -> pj_apartR D p.
Proof. intros m lblk d p D F H. destruct d; cbn [pj_foR pj_oshapeR] in H; exact (proj1 (proj2 H)). Qed.

(* a node with its order list, moved to p' (header bytes copied, writable kept), its blocks unchanged: the twin of
   PItems_shape.pis_node_xfer *)
Lemma pis_fo_node_xfer : forall d m lblk m' lblk' p p' D F,
  pj_foR segs m lblk d p D F ->
  (forall a k, In (a, k) D -> lblk' a k) ->
  (forall x, (exists b, In b D /\ pj_holdsR b x) -> pis_same segs m m' x) ->
  p' mod 8 = 0 ->
  (forall i, 0 <= i < 56 -> mbyte segs m' (p' + i) = mbyte segs m (p + i)) ->
  (forall i, 0 <= i < 56 -> writable_at segs m (p + i) -> writable_at segs m' (p' + i)) ->
  pj_apartR D p' ->
  pj_foR segs m' lblk' d p' D F.
Proof.
  intros d m lblk m' lblk' p p' D F H HL HM Ha' E W Hap.
  destruct d as [|d]; cbn [pj_foR] in H |- *; unfold pj_oshapeR in H |- *;
    destruct H as (Hnd & _ & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & Fi &
      Hh & Hs & Hk & Hy & Hp & HPi & ->);
    (assert (HinD : forall b, In b (Ds ++ Dk ++ Dy ++ Di) -> In b D)
       by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact Hp | exact Hb]));
    (split; [exact Hnd|]); (split; [exact Hap|]);
    exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di, Fi;
    (split; [exact (pis_hdr_mv segs m m' p p' ty num str kids keys n cap Hh Ha' E W)|]);
    (split; [destruct Hs as [Hs|(k & _ & ->)]; [left; exact Hs|];
             right; exists k; split; [|reflexivity];
             apply HL; apply HinD; apply in_or_app; left; apply in_eq|]);
    (split; [destruct Hk as [Hk'|(k & _ & Hnk & ->)]; [left; exact Hk'|];
             right; exists k; split; [|split; [exact Hnk | reflexivity]];
             apply HL; apply HinD; apply in_or_app; right; apply in_or_app; left; apply in_eq|]);
    (split; [destruct Hy as [Hy'|(Hks & k & _ & Hnk & ->)]; [left; exact Hy'|];
             right; split; [exact Hks|]; exists k; split; [|split; [exact Hnk | reflexivity]];
             apply HL; apply HinD; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left;
             apply in_eq|]);
    (split; [exact Hp|]); (split; [|reflexivity]).
  - exact HPi.
  - cbv beta in HPi |- *.
    apply (pf_oitemsR_frame segs d m m' lblk lblk' ks kids keys (Z.to_nat n) Di Fi HPi).
    + intros x k Hin. apply HL. apply HinD. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
      exact Hin.
    + intros y Hy'. apply HM. unfold pf_ofoot in Hy'. destruct Hy' as [Hy'|[(Hks & Hy')|(b & Hb & Hy')]].
      * destruct Hk as [(-> & -> & ->)|(k & _ & Hnk & ->)]; [cbn in Hy'; clear - Hy'; lia|].
        exists (kids, k). split; [apply HinD; apply in_or_app; right; apply in_or_app; left; apply in_eq|].
        unfold pj_holdsR; cbn [fst snd]. clear - Hy' Hnk; lia.
      * destruct Hy as [(-> & -> & ->)|(_ & k & _ & Hnk & ->)]; [discriminate Hks|].
        exists (keys, k).
        split; [apply HinD; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; apply in_eq|].
        unfold pj_holdsR; cbn [fst snd]. clear - Hy' Hnk; lia.
      * exists b. split; [|exact Hy']. apply HinD. apply in_or_app. right. apply in_or_app. right.
        apply in_or_app. right. exact Hb.
Qed.

(* an order list moved with its slot arrays (kids a -> a', keys ka -> ka'), the slot blocks unchanged: the twin of
   PItems_shape.pis_items_xfer (a' = a, ka' = ka is the frame of a kept grow) *)
Lemma pis_fo_items_xfer : forall d m lblk m' lblk' ks a ka a' ka' n D F,
  pf_oitemsR segs m lblk (pj_foR segs m lblk d) ks a ka n D F ->
  (forall x k, In (x, k) D -> lblk' x k) ->
  (forall x, (exists b, In b D /\ pj_holdsR b x) -> pis_same segs m m' x) ->
  pis_moved segs m m' a a' (56 * Z.of_nat n) ->
  (forall i, 0 <= i < 56 * Z.of_nat n -> writable_at segs m (a + i) -> writable_at segs m' (a' + i)) ->
  ((0 < n)%nat -> a' mod 8 = 0) ->
  (a' = a \/ pis_apart_n D a' (56 * Z.of_nat n)) ->
  (ks = true -> pis_moved segs m m' ka ka' (8 * Z.of_nat n)) ->
  pf_oitemsR segs m' lblk' (pj_foR segs m' lblk' d) ks a' ka' n D F.
Proof.
  intros d m lblk m' lblk' ks a ka a' ka' n. revert a ka a' ka'.
  induction n as [|n IH]; intros a ka a' ka' D F H HL HM Hmv HW H8 Hap Hy;
    cbn [pf_oitemsR] in H |- *; [exact H|].
  destruct H as (Dk & D1 & F1 & D2 & F2 & -> & -> & Hk & H1 & H2).
  exists Dk, D1, F1, D2, F2. split; [reflexivity|]. split; [reflexivity|]. split; [|split].
  - unfold pj_keyR in Hk |- *. destruct ks; cbv beta iota in Hk |- *; [|exact Hk].
    destruct Hk as (x & Hx & Hc). exists x. split.
    + apply (pis_u64_mv segs m m' ka ka' x Hx). intros i Hi. apply (Hy eq_refl). clear - Hi; lia.
    + destruct Hc as [Hc|(k & Hl & ->)]; [left; exact Hc|]. right. exists k. split; [|reflexivity].
      apply HL. apply in_or_app. left. apply in_eq.
  - apply (pis_fo_node_xfer d m lblk m' lblk' a a' D1 F1 H1).
    + intros x k Hin. apply HL. apply in_or_app. right. apply in_or_app. left. exact Hin.
    + intros x (b & Hb & Hx). apply HM. exists b. split; [|exact Hx].
      apply in_or_app. right. apply in_or_app. left. exact Hb.
    + apply H8. clear; lia.
    + intros i Hi. apply Hmv. clear - Hi; lia.
    + intros i Hi Hw. apply HW; [clear - Hi; lia | exact Hw].
    + destruct Hap as [->|Hap]; [exact (pis_fo_apart m lblk d a D1 F1 H1)|].
      intros b x Hb Hx Hx'. apply (Hap b x).
      * apply in_or_app. right. apply in_or_app. left. exact Hb.
      * exact Hx.
      * clear - Hx'; lia.
  - apply (IH (a + 56) (ka + 8) (a' + 56) (ka' + 8) D2 F2 H2).
    + intros x k Hin. apply HL. apply in_or_app. right. apply in_or_app. right. exact Hin.
    + intros x (b & Hb & Hx). apply HM. exists b. split; [|exact Hx].
      apply in_or_app. right. apply in_or_app. right. exact Hb.
    + intros i Hi.
      replace (a' + 56 + i) with (a' + (56 + i)) by (clear; lia).
      replace (a + 56 + i) with (a + (56 + i)) by (clear; lia).
      apply Hmv. clear - Hi; lia.
    + intros i Hi Hw. replace (a' + 56 + i) with (a' + (56 + i)) by (clear; lia).
      apply HW; [clear - Hi; lia|]. replace (a + (56 + i)) with (a + 56 + i) by (clear; lia). exact Hw.
    + intros _. replace (a' + 56) with (a' + 7 * 8) by (clear; lia). rewrite Z_mod_plus_full.
      apply H8. clear; lia.
    + destruct Hap as [->|Hap]; [left; reflexivity|right].
      intros b x Hb Hx Hx'. apply (Hap b x).
      * apply in_or_app. right. apply in_or_app. right. exact Hb.
      * exact Hx.
      * clear - Hx'; lia.
    + intros Eks i Hi.
      replace (ka' + 8 + i) with (ka' + (8 + i)) by (clear; lia).
      replace (ka + 8 + i) with (ka + (8 + i)) by (clear; lia).
      apply (Hy Eks). clear - Hi; lia.
Qed.

(* one more completed slot at the end of an order list: its subtree's list, then its key (pf_oitemsR's S case) *)
Lemma pis_fo_snoc_gen : forall m lblk (P : Z -> list (Z * Z) -> list (Z * Z) -> Prop) ks a ka n D F Dn Dt Ft,
  pf_oitemsR segs m lblk P ks a ka n D F ->
  pj_keyR segs m lblk ks (ka + 8 * Z.of_nat n) Dn ->
  P (a + 56 * Z.of_nat n) Dt Ft ->
  pf_oitemsR segs m lblk P ks a ka (S n) (D ++ Dn ++ Dt) (F ++ Ft ++ Dn).
Proof.
  intros m lblk P ks a ka n. revert a ka.
  induction n as [|n IH]; intros a ka D F Dn Dt Ft H Hk HP.
  - cbn [pf_oitemsR] in H |- *. destruct H as [-> ->]. exists Dn, Dt, Ft, [], [].
    replace (ka + 8 * Z.of_nat 0) with ka in Hk by (clear; lia).
    replace (a + 56 * Z.of_nat 0) with a in HP by (clear; lia).
    split; [rewrite app_nil_r; reflexivity|]. split; [rewrite app_nil_r; reflexivity|].
    split; [exact Hk|]. split; [exact HP | split; reflexivity].
  - cbn [pf_oitemsR] in H. destruct H as (Dk0 & D10 & F10 & D20 & F20 & -> & -> & Hk0 & HP0 & HR).
    exists Dk0, D10, F10, (D20 ++ Dn ++ Dt), (F20 ++ Ft ++ Dn).
    split; [rewrite <- !app_assoc; reflexivity|]. split; [rewrite <- !app_assoc; reflexivity|].
    split; [exact Hk0|]. split; [exact HP0|].
    apply (IH (a + 56) (ka + 8) D20 F20 Dn Dt Ft HR).
    + replace (ka + 8 + 8 * Z.of_nat n) with (ka + 8 * Z.of_nat (S n)) by (clear; lia). exact Hk.
    + replace (a + 56 + 56 * Z.of_nat n) with (a + 56 * Z.of_nat (S n)) by (clear; lia). exact HP.
Qed.

(* THE SNOC: slot n's value subtree (Ft) and key (Dn) appended to the completed slots' order list *)
Lemma pis_fo_snoc : forall m lblk nn ks a ka n D F Dn Dt Ft,
  pf_oitemsR segs m lblk (pj_foR segs m lblk nn) ks a ka n D F ->
  pj_keyR segs m lblk ks (ka + 8 * Z.of_nat n) Dn ->
  pj_foR segs m lblk nn (a + 56 * Z.of_nat n) Dt Ft ->
  pf_oitemsR segs m lblk (pj_foR segs m lblk nn) ks a ka (S n) (D ++ Dn ++ Dt) (F ++ Ft ++ Dn).
Proof.
  intros m lblk nn ks a ka n D F Dn Dt Ft H Hk Ht.
  exact (pis_fo_snoc_gen m lblk (pj_foR segs m lblk nn) ks a ka n D F Dn Dt Ft H Hk Ht).
Qed.

(* the node of an open container from its parts: N completed slots with order list Facc, then kids, then keys *)
Lemma pis_fo_shape : forall m lblk v o num kids keys cap (N : nat) Di nn Facc,
  NoDup (pis_slots o kids keys cap ++ Di) -> pj_apartR (pis_slots o kids keys cap ++ Di) v ->
  pj_hdrR segs m v (5 + pis_oz o) num 0 kids keys (Z.of_nat N) cap ->
  pj_slots_atR lblk (5 + pis_oz o) kids keys (Z.of_nat N) cap -> (o = false -> keys = 0) ->
  pf_oitemsR segs m lblk (pj_foR segs m lblk nn) o kids keys N Di Facc ->
  pj_foR segs m lblk (S nn) v (pis_slots o kids keys cap ++ Di) (Facc ++ pis_slots o kids keys cap).
Proof.
  intros m lblk v o num kids keys cap N Di nn Facc HN HA Hh Hs Hk HI.
  destruct Hs as (_ & (Hn1 & _) & Hc0 & Hcp).
  cbn [pj_foR]. unfold pj_oshapeR. split; [exact HN|]. split; [exact HA|].
  destruct (Z.eq_dec cap 0) as [E0|E0].
  - subst cap. destruct (Hc0 eq_refl) as (K0 & Y0).
    assert (Ky : keys = 0) by (destruct o; [apply Y0; reflexivity | apply Hk; reflexivity]).
    assert (EN : N = 0%nat) by (clear - Hn1; lia).
    subst N. cbn [pf_oitemsR] in HI. destruct HI as [-> ->].
    assert (ES : pis_slots o kids keys 0 = []) by (unfold pis_slots, kids_blkR, keys_blkR; reflexivity).
    rewrite ES.
    exists (5 + pis_oz o), num, 0, kids, keys, (Z.of_nat 0), 0, false, [], [], [], [], [].
    split; [exact Hh|]. split; [left; split; reflexivity|].
    split; [left; split; [exact K0 | split; reflexivity]|].
    split; [left; split; [exact Ky | split; reflexivity]|].
    split; [apply Permutation_refl|].
    split; [cbn; split; reflexivity | reflexivity].
  - destruct (Hcp ltac:(clear - Hn1 E0; lia)) as (L0 & L1).
    assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; exact E0).
    destruct o.
    + assert (ES : pis_slots true kids keys cap = [(kids, 56 * cap); (keys, 8 * cap)])
        by (unfold pis_slots, kids_blkR, keys_blkR; rewrite Ec; reflexivity).
      rewrite ES.
      exists (5 + pis_oz true), num, 0, kids, keys, (Z.of_nat N), cap, true, [], [(kids, 56 * cap)],
        [(keys, 8 * cap)], Di, Facc.
      split; [exact Hh|]. split; [left; split; reflexivity|].
      split; [right; exists (56 * cap); split; [exact L0 | split; [clear - Hn1; lia | reflexivity]]|].
      split; [right; split; [reflexivity|]; exists (8 * cap);
              split; [apply L1; reflexivity | split; [clear - Hn1; lia | reflexivity]]|].
      split; [apply Permutation_refl|].
      split; [cbv beta; rewrite Nat2Z.id; exact HI | reflexivity].
    + assert (ES : pis_slots false kids keys cap = [(kids, 56 * cap)])
        by (unfold pis_slots, kids_blkR, keys_blkR; rewrite Ec; reflexivity).
      rewrite ES.
      exists (5 + pis_oz false), num, 0, kids, keys, (Z.of_nat N), cap, false, [], [(kids, 56 * cap)], [], Di, Facc.
      split; [exact Hh|]. split; [left; split; reflexivity|].
      split; [right; exists (56 * cap); split; [exact L0 | split; [clear - Hn1; lia | reflexivity]]|].
      split; [left; split; [apply Hk; reflexivity | split; reflexivity]|].
      split; [apply Permutation_refl|].
      split; [cbv beta; rewrite Nat2Z.id; exact HI | reflexivity].
Qed.

(* ==== THE EXITS ==== *)

(* the twin of pis_exit_open: the open container, its completed slots' order list Facc *)
Lemma pis_fo_open : forall m lblk v o num kids keys cap ts ns Di nn Facc,
  pis_open segs m lblk v o num kids keys cap (Z.of_nat (length ts)) ts ns Di ->
  pf_oitemsR segs m lblk (pj_foR segs m lblk nn) o kids keys (length ts) Di Facc ->
  pj_foR segs m lblk (S nn) v (pis_slots o kids keys cap ++ Di) (Facc ++ pis_slots o kids keys cap).
Proof.
  intros m lblk v o num kids keys cap ts ns Di nn Facc (HN & HA & Hh & Hs & Hk & _) HI.
  exact (pis_fo_shape m lblk v o num kids keys cap (length ts) Di nn Facc HN HA Hh Hs Hk HI).
Qed.

(* the twin of pis_exit_grow_kept: a refused grow that kept both arrays; Facc at the OLD memory m *)
Lemma pis_fo_grow_kept : forall m m' lblk v o num kids keys cap ts ns Di nn Facc,
  pis_open segs m lblk v o num kids keys cap (Z.of_nat (length ts)) ts ns Di ->
  pj_hdrR segs m' v (5 + pis_oz o) num 0 kids keys (Z.of_nat (length ts)) cap ->
  pis_moved segs m m' kids kids (56 * cap) -> (o = true -> pis_moved segs m m' keys keys (8 * cap)) ->
  (forall i, 0 <= i < 56 * Z.of_nat (length ts) -> writable_at segs m (kids + i) -> writable_at segs m' (kids + i)) ->
  (forall x, (exists b, In b Di /\ pj_holdsR b x) -> pis_same segs m m' x) ->
  pf_oitemsR segs m lblk (pj_foR segs m lblk nn) o kids keys (length ts) Di Facc ->
  pj_foR segs m' lblk (S nn) v (pis_slots o kids keys cap ++ Di) (Facc ++ pis_slots o kids keys cap).
Proof.
  intros m m' lblk v o num kids keys cap ts ns Di nn Facc H Hh' Hmk Hmy HW HM HI.
  pose proof H as (_ & _ & _ & (_ & (Hn1 & _) & _) & _ & Hi).
  apply (pis_fo_open m' lblk v o num kids keys cap ts ns Di nn Facc).
  - exact (pis_grow_kept segs m m' lblk v o num kids keys cap _ ts ns Di H Hh' Hmk Hmy HW HM Hn1).
  - apply (pis_fo_items_xfer nn m lblk m' lblk o kids keys kids keys (length ts) Di Facc HI).
    + exact (pis_items_lblk segs m lblk o kids keys ts ns Di Hi).
    + exact HM.
    + intros i Hi'. apply Hmk. clear - Hi' Hn1; lia.
    + exact HW.
    + intros Hl. exact (pis_items_mod8 segs m lblk o kids keys ts ns Di Hi Hl).
    + left. reflexivity.
    + intros Eo i Hi'. apply (Hmy Eo). clear - Hi' Hn1; lia.
Qed.

(* the twin of pis_exit_grow_half: an object's grow that moved kids to the new block k' and was refused the keys
   realloc; the node then holds the new kids block and the old keys block (PresetReqAt.gheld's first arm) *)
Lemma pis_fo_grow_half : forall m m' Lam Lam' Lam0 v num kids keys cap ts ns Di k' nn Facc,
  pis_open segs m (prh_lin Lam) v true num kids keys cap (Z.of_nat (length ts)) ts ns Di ->
  Permutation Lam (kids_blkR kids cap ++ Lam0) -> Permutation Lam' ((k', 56 * cap2R cap) :: Lam0) ->
  NoDup (map fst Lam') ->
  pis_moved segs m m' kids k' (56 * cap) -> pis_moved segs m m' keys keys (8 * cap) ->
  pj_hdrR segs m' v 6 num 0 k' keys (Z.of_nat (length ts)) cap ->
  k' mod 8 = 0 ->
  (forall i, 0 <= i < 56 * Z.of_nat (length ts) -> writable_at segs m' (k' + i)) ->
  (forall x, (exists b, In b Di /\ pj_holdsR b x) -> pis_same segs m m' x) ->
  pis_apart_n Di k' (56 * Z.of_nat (length ts)) ->
  pj_apartR [(k', 56 * cap2R cap)] v ->
  pf_oitemsR segs m (prh_lin Lam) (pj_foR segs m (prh_lin Lam) nn) true kids keys (length ts) Di Facc ->
  pj_foR segs m' (prh_lin Lam') (S nn) v ((k', 56 * cap2R cap) :: keys_blkR 6 keys cap ++ Di)
    (Facc ++ (k', 56 * cap2R cap) :: keys_blkR 6 keys cap).
Proof.
  intros m m' Lam Lam' Lam0 v num kids keys cap ts ns Di k' nn Facc H HP HP' HN' Hmk Hmy Hh' Hk8 HW HM Hap Hav HI.
  pose proof H as (HN & HA & _ & Hs & _ & _).
  destruct Hs as (_ & (Hn1 & _) & Hc0 & Hcp).
  assert (HR : incl (keys_blkR 6 keys cap ++ Di) Lam0).
  { apply (pis_rest (kids_blkR kids cap) (keys_blkR 6 keys cap ++ Di) Lam Lam0); [| |exact HP].
    - rewrite app_assoc. exact HN.
    - rewrite app_assoc. exact (pis_open_incl segs m Lam v true num kids keys cap _ ts ns Di H). }
  assert (HL' : forall a k, In (a, k) Lam0 -> prh_lin Lam' a k)
    by (intros a k Hak; unfold prh_lin; apply (Permutation_in _ (Permutation_sym HP')); right; exact Hak).
  assert (HI' : pf_oitemsR segs m' (prh_lin Lam') (pj_foR segs m' (prh_lin Lam') nn) true k' keys (length ts) Di Facc).
  { apply (pis_fo_items_xfer nn m (prh_lin Lam) m' (prh_lin Lam') true kids keys k' keys (length ts) Di Facc HI).
    - intros a k Hak. apply HL'. apply HR. apply in_or_app. right. exact Hak.
    - exact HM.
    - intros i Hi'. apply Hmk. clear - Hi' Hn1; lia.
    - intros i Hi' _. exact (HW i Hi').
    - intros _. exact Hk8.
    - right. exact Hap.
    - intros _ i Hi'. apply Hmy. clear - Hi' Hn1; lia. }
  assert (Hkk : prh_lin Lam' k' (56 * cap2R cap))
    by (unfold prh_lin; apply (Permutation_in _ (Permutation_sym HP')); left; reflexivity).
  assert (Hc2 : cap <= cap2R cap)
    by (unfold cap2R; destruct (Z.eqb_spec cap 0) as [Ez|Ez]; clear - Hn1 Ez; lia).
  cbn [pj_foR]. unfold pj_oshapeR.
  split.
  { apply (pis_nodup_new [(k', 56 * cap2R cap)] (keys_blkR 6 keys cap ++ Di) Lam' Lam0 HN' HP' HR).
    apply (pis_nodup_r _ (kids_blkR kids cap) (keys_blkR 6 keys cap ++ Di)). rewrite app_assoc. exact HN. }
  split.
  { change (pj_apartR ([(k', 56 * cap2R cap)] ++ (keys_blkR 6 keys cap ++ Di)) v).
    apply pis_r_apart_app; [exact Hav|].
    intros b x Hb. apply (HA b x). unfold pis_slots. rewrite <- app_assoc. apply in_or_app. right. exact Hb. }
  destruct (Z.eq_dec cap 0) as [E0|E0].
  - subst cap. destruct (Hc0 eq_refl) as (K0 & Y0). specialize (Y0 eq_refl).
    assert (Hl0 : length ts = 0%nat) by (clear - Hn1; lia).
    rewrite Hl0 in Hh', HI'. cbn [pf_oitemsR] in HI'. destruct HI' as [-> ->].
    exists 6, num, 0, k', keys, (Z.of_nat 0), 0, false, [], [(k', 56 * cap2R 0)], [], [], [].
    split; [exact Hh'|]. split; [left; split; reflexivity|].
    split; [right; exists (56 * cap2R 0); split; [exact Hkk | split; [change (cap2R 0) with 8; clear; lia | reflexivity]]|].
    split; [left; split; [exact Y0 | split; reflexivity]|].
    split; [unfold keys_blkR; cbn; apply Permutation_refl|].
    split; [cbn; split; reflexivity | unfold keys_blkR; cbn; reflexivity].
  - destruct (Hcp ltac:(clear - Hn1 E0; lia)) as (L0 & L1).
    assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; exact E0).
    assert (EY : keys_blkR 6 keys cap = [(keys, 8 * cap)]) by (unfold keys_blkR; rewrite Ec; reflexivity).
    assert (Hky : In (keys, 8 * cap) Lam0) by (apply HR; apply in_or_app; left; rewrite EY; left; reflexivity).
    rewrite EY.
    exists 6, num, 0, k', keys, (Z.of_nat (length ts)), cap, true, [], [(k', 56 * cap2R cap)], [(keys, 8 * cap)],
      Di, Facc.
    split; [exact Hh'|]. split; [left; split; reflexivity|].
    split; [right; exists (56 * cap2R cap); split; [exact Hkk | split; [clear - Hn1 Hc2; lia | reflexivity]]|].
    split; [right; split; [reflexivity|]; exists (8 * cap);
            split; [exact (HL' _ _ Hky) | split; [clear - Hn1; lia | reflexivity]]|].
    split; [apply Permutation_refl|].
    split; [cbv beta; rewrite Nat2Z.id; exact HI' | reflexivity].
Qed.

(* the twin of pis_exit_item: slot n's value (Dt, order list Ft) and key (Dn) completed, n++ stored (m -> m'); the
   order list is Facc, then slot n (its subtree, then its key), then the arrays *)
Lemma pis_fo_item : forall m m' lblk v o num kids keys cap ts ns Di nn Facc Dn Dt Ft,
  pis_open segs m lblk v o num kids keys cap (Z.of_nat (length ts)) ts ns Di ->
  Z.of_nat (length ts) < cap ->
  pf_oitemsR segs m lblk (pj_foR segs m lblk nn) o kids keys (length ts) Di Facc ->
  pj_foR segs m lblk nn (kids + 56 * Z.of_nat (length ts)) Dt Ft ->
  (if o then pj_keyR segs m lblk true (keys + 8 * Z.of_nat (length ts)) Dn else Dn = []) ->
  NoDup (pis_slots o kids keys cap ++ Di ++ Dn ++ Dt) -> pj_apartR (Dn ++ Dt) v ->
  pj_hdrR segs m' v (5 + pis_oz o) num 0 kids keys (Z.of_nat (length ts) + 1) cap ->
  (forall x, pis_ifoot o kids keys (Z.of_nat (length ts) + 1) (Di ++ Dt) x -> pis_same segs m m' x) ->
  pj_foR segs m' lblk (S nn) v (pis_slots o kids keys cap ++ Di ++ Dn ++ Dt)
    ((Facc ++ Ft ++ Dn) ++ pis_slots o kids keys cap).
Proof.
  intros m m' lblk v o num kids keys cap ts ns Di nn Facc Dn Dt Ft H Hlc HI Ht Hn HN HA Hh' HM.
  pose proof H as (_ & HA0 & _ & _ & Hk & _).
  assert (H' : pis_open segs m' lblk v o num kids keys cap (Z.of_nat (length ts) + 1) ts ns Di).
  { refine (pis_frame_v segs m lblk m' v o num kids keys cap _ ts ns Di num _ H Hh' ltac:(clear - Hlc; lia) _).
    intros x Hx. apply HM. destruct Hx as [Hx|[(Eo & Hx)|(b & Hb & Hx)]].
    - left. clear - Hx; lia.
    - right. left. split; [exact Eo | clear - Hx; lia].
    - right. right. exists b. split; [apply in_or_app; left; exact Hb | exact Hx]. }
  pose proof H' as (_ & _ & _ & Hs' & _).
  assert (HI' : pf_oitemsR segs m' lblk (pj_foR segs m' lblk nn) o kids keys (length ts) Di Facc).
  { apply (pf_oitemsR_frame segs nn m m' lblk lblk o kids keys (length ts) Di Facc HI).
    - exact (pf_oitemsR_lblk segs m lblk nn o kids keys (length ts) Di Facc HI).
    - intros y Hy. apply HM. unfold pf_ofoot in Hy. destruct Hy as [Hy|[(Eo & Hy)|(b & Hb & Hy)]].
      + left. clear - Hy; lia.
      + right. left. split; [exact Eo | clear - Hy; lia].
      + right. right. exists b. split; [apply in_or_app; left; exact Hb | exact Hy]. }
  assert (Ht' : pj_foR segs m' lblk nn (kids + 56 * Z.of_nat (length ts)) Dt Ft).
  { apply (pj_foR_frame segs nn m m' lblk lblk _ Dt Ft Ht).
    - exact (pj_foR_lblk segs m lblk nn _ Dt Ft Ht).
    - intros y Hy. apply HM. unfold pj_footR in Hy. destruct Hy as [Hy|(b & Hb & Hy)].
      + left. clear - Hy; lia.
      + right. right. exists b. split; [apply in_or_app; right; exact Hb | exact Hy]. }
  assert (Hn' : pj_keyR segs m' lblk o (keys + 8 * Z.of_nat (length ts)) Dn).
  { destruct o; [|exact Hn].
    cbn [pj_keyR] in Hn |- *. destruct Hn as (x & Hx & Hz). exists x. split; [|exact Hz].
    apply (pis_u64_frame segs m m'); [exact Hx|]. intros y Hy. refine (proj1 (HM y _)).
    right. left. split; [reflexivity | clear - Hy; lia]. }
  pose proof (pis_fo_snoc m' lblk nn o kids keys (length ts) Di Facc Dn Dt Ft HI' Hn' Ht') as HS.
  assert (EN : Z.of_nat (length ts) + 1 = Z.of_nat (S (length ts))) by (clear; lia).
  rewrite EN in Hh'. rewrite EN in Hs'.
  apply (pis_fo_shape m' lblk v o num kids keys cap (S (length ts)) (Di ++ Dn ++ Dt) nn (Facc ++ Ft ++ Dn) HN).
  - rewrite app_assoc. apply pis_r_apart_app; [exact HA0 | exact HA].
  - exact Hh'.
  - exact Hs'.
  - exact Hk.
  - exact HS.
Qed.

(* the twin of pis_close at the closer (the Some arm): the container of acc, in pis_close's form *)
Lemma pis_fo_close : forall m lblk v o num kids keys cap (acc : list (list Z * jv)) Di nn Facc,
  pis_open segs m lblk v o num kids keys cap (Z.of_nat (length acc)) (map snd (rev acc)) (map fst (rev acc)) Di ->
  pf_oitemsR segs m lblk (pj_foR segs m lblk nn) o kids keys (length acc) Di Facc ->
  pj_foR segs m lblk (S nn) v (pis_slots o kids keys cap ++ Di) (Facc ++ pis_slots o kids keys cap).
Proof.
  intros m lblk v o num kids keys cap acc Di nn Facc (HN & HA & Hh & Hs & Hk & _) HI.
  exact (pis_fo_shape m lblk v o num kids keys cap (length acc) Di nn Facc HN HA Hh Hs Hk HI).
Qed.

End fo.

(* ==== THE SIZES: the arrays' requests against the kit's model, at any head hd = PresetReqAt.HEAD (pi_forder's and the
   post's `fun b => snd b + cf_head` under prh_head16) ==== *)

(* the arrays of an open container (kept, or after a granted grow): PresetReqAt.arrz, kids then keys *)
Lemma pis_fo_slots_hb : forall hd o kids keys cap, hd = PresetReqAt.HEAD -> 0 <= cap ->
  map (fun b => snd b + hd) (pis_slots o kids keys cap) = PresetReqAt.arrz o (Z.to_nat cap).
Proof.
  intros hd o kids keys cap -> Hc. unfold pis_slots, kids_blkR, keys_blkR, PresetReqAt.arrz.
  destruct (Z.eqb_spec cap 0) as [->|E0]; [destruct o; reflexivity|].
  destruct (Z.to_nat cap) as [|c] eqn:Ec; [clear - Hc E0 Ec; lia|].
  assert (E56 : Z.of_nat (56 * S c) = 56 * cap) by (clear - Hc Ec; lia).
  assert (E8 : Z.of_nat (8 * S c) = 8 * cap) by (clear - Hc Ec; lia).
  rewrite E56, E8. destruct o; reflexivity.
Qed.

(* the same at pi_cont's natural cap *)
Lemma pis_fo_slots_hb_nat : forall hd o kids keys (cap : nat), hd = PresetReqAt.HEAD ->
  map (fun b => snd b + hd) (pis_slots o kids keys (Z.of_nat cap)) = PresetReqAt.arrz o cap.
Proof.
  intros hd o kids keys cap Hh.
  rewrite (pis_fo_slots_hb hd o kids keys (Z.of_nat cap) Hh (Nat2Z.is_nonneg cap)), Nat2Z.id. reflexivity.
Qed.

(* a grow refused at its first realloc keeps both arrays: gheld's default arm *)
Lemma pis_fo_kept_hb : forall hd o kids keys cap f, hd = PresetReqAt.HEAD -> 0 <= cap ->
  map (fun b => snd b + hd) (pis_slots o kids keys cap) = PresetReqAt.gheld o (Z.to_nat cap) [EFail f].
Proof. intros hd o kids keys cap f Hh Hc. rewrite (pis_fo_slots_hb hd o kids keys cap Hh Hc). reflexivity. Qed.

(* a grow that moved kids (realloc to g1 = 56 * cap2R cap bytes) and was refused the keys: gheld's first arm *)
Lemma pis_fo_half_hb : forall hd o keys cap k' (g0 g1 f : nat), hd = PresetReqAt.HEAD -> 0 <= cap ->
  Z.of_nat g1 = 56 * cap2R cap ->
  map (fun b => snd b + hd) ((k', 56 * cap2R cap) :: keys_blkR 6 keys cap) =
  PresetReqAt.gheld o (Z.to_nat cap) [EGrow g0 g1; EFail f].
Proof.
  intros hd o keys cap k' g0 g1 f -> Hc Eg. unfold PresetReqAt.gheld, keys_blkR. cbn [map fst snd].
  rewrite Eg. f_equal.
  destruct (Z.eqb_spec cap 0) as [->|E0]; [reflexivity|].
  destruct (Z.to_nat cap) as [|c] eqn:Ec; [clear - Hc E0 Ec; lia|].
  assert (E8 : Z.of_nat (8 * S c) = 8 * cap) by (clear - Hc Ec; lia).
  rewrite E8. reflexivity.
Qed.

(* ==== THE DEPTH BOUND: pi_forder's nn-form to the post's n-form (n = S nn) ==== *)
Lemma pi_forder_post : forall (d : nat) (P : nat -> Prop), (d < MAXD)%nat ->
  (forall nn, (MAXD - S d <= nn)%nat -> P (S nn)) ->
  forall n, (MAXD - d <= n)%nat -> P n.
Proof.
  intros d P Hd HP n Hn. destruct n as [|nn]; [clear - Hd Hn; lia|].
  apply HP. clear - Hd Hn; lia.
Qed.

(* the closer's depth: a container of the members acc fits depth n' exactly when n' = S nn with every member at
   most nn deep *)
Lemma pi_forder_mk : forall o (acc : list (list Z * jv)) n', (depth (mk o (rev acc)) <= n')%nat ->
  exists nn, n' = S nn /\ Forall (fun mb => (depth (snd mb) <= nn)%nat) acc.
Proof.
  intros o acc n' H. destruct n' as [|nn].
  - exfalso. destruct o; unfold mk in H; cbn [depth] in H; clear - H; lia.
  - exists nn. split; [reflexivity|]. apply Forall_forall. intros [nm u] Hin. cbn [snd].
    apply in_rev in Hin. destruct o; unfold mk in H.
    + pose proof (depth_member (rev acc) nm u Hin) as Hd. clear - H Hd; lia.
    + pose proof (depth_item (map snd (rev acc)) u (in_map snd (rev acc) (nm, u) Hin)) as Hd. clear - H Hd; lia.
Qed.

(* pi_forder (PItems_defs.v) at a REFUSAL exit's post depth n' >= MAXD - d: n' = S nn with nn >= MAXD - S d (the
   depth the refused member's own post gives its order list at), and the completed slots' order list at nn; the loop
   pres' Forall (depth <= MAXD - S d) acc covers the members *)
Lemma pi_forder_at {cp : YGcfNames.CfParams} {rc : YM05.RunCeil} {L} {PA : YC4aP.PAImg L} :
  forall m lblk o kids keys n Di acc af d,
  PItems_defs.pi_forder m lblk o kids keys n Di acc af -> YGcfNames.cf_head = PresetReqAt.HEAD -> (d < MAXD)%nat ->
  Forall (fun mb => (depth (snd mb) <= MAXD - S d)%nat) acc ->
  forall n', (MAXD - d <= n')%nat ->
  exists nn Facc, n' = S nn /\ (MAXD - S d <= nn)%nat /\
    pf_oitemsR YC4aP.pa_segs m lblk (pj_foR YC4aP.pa_segs m lblk nn) o kids keys n Di Facc /\
    map (fun b => snd b + YGcfNames.cf_head) Facc = af.
Proof.
  intros m lblk o kids keys n Di acc af d HF HH Hd HA n' Hn'.
  destruct n' as [|nn]; [clear - Hd Hn'; lia|].
  assert (Hnn : (MAXD - S d <= nn)%nat) by (clear - Hd Hn'; lia).
  assert (HA' : Forall (fun mb => (depth (snd mb) <= nn)%nat) acc).
  { eapply Forall_impl; [|exact HA]. intros mb Hmb. cbv beta in Hmb |- *. clear - Hmb Hnn; lia. }
  destruct (HF HH nn HA') as (Facc & HI & HM).
  exists nn, Facc. split; [reflexivity|]. split; [exact Hnn|]. split; [exact HI | exact HM].
Qed.

(* pi_forder at the CLOSER's post depth n' >= depth (mk o (rev acc)) (the Some arm): n' = S nn, every member at most
   nn deep, and the completed slots' order list at nn *)
Lemma pi_forder_close {cp : YGcfNames.CfParams} {rc : YM05.RunCeil} {L} {PA : YC4aP.PAImg L} :
  forall m lblk o kids keys n Di acc af,
  PItems_defs.pi_forder m lblk o kids keys n Di acc af -> YGcfNames.cf_head = PresetReqAt.HEAD ->
  forall n', (depth (mk o (rev acc)) <= n')%nat ->
  exists nn Facc, n' = S nn /\ Forall (fun mb => (depth (snd mb) <= nn)%nat) acc /\
    pf_oitemsR YC4aP.pa_segs m lblk (pj_foR YC4aP.pa_segs m lblk nn) o kids keys n Di Facc /\
    map (fun b => snd b + YGcfNames.cf_head) Facc = af.
Proof.
  intros m lblk o kids keys n Di acc af HF HH n' Hn'.
  destruct (pi_forder_mk o acc n' Hn') as (nn & -> & HA).
  destruct (HF HH nn HA) as (Facc & HI & HM).
  exists nn, Facc. split; [reflexivity|]. split; [exact HA|]. split; [exact HI | exact HM].
Qed.
