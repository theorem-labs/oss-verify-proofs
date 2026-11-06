(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk MemSplit Hoare RefMemcpyLib LibIface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Facts.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.

Definition agree_on (M M' : mem) (a n : Z) : Prop :=
  forall i, 0 <= i < n -> M' (Z_to_bv 64 (a + i)) = M (Z_to_bv 64 (a + i)).

Lemma agree_on_sub : forall M M' a n b m,
  agree_on M M' a n -> a <= b -> b + m <= a + n -> agree_on M M' b m.
Proof using. intros M M' a n b m H Hab Hbm i Hi. replace (b + i) with (a + (b - a + i)) by lia. apply H. lia. Qed.

Lemma agree_on_refl : forall M a n, agree_on M M a n.
Proof using. intros M a n i Hi. reflexivity. Qed.

Lemma agree_on_trans : forall M1 M2 M3 a n, agree_on M1 M2 a n -> agree_on M2 M3 a n -> agree_on M1 M3 a n.
Proof using. intros M1 M2 M3 a n H1 H2 i Hi. rewrite (H2 i Hi). apply H1. exact Hi. Qed.

Lemma cellw_agree : forall M M' a (w : N) v,
  cellw SEGS M a w v -> agree_on M M' a (Z.of_N w) -> 0 <= a < 2 ^ 64 -> a + Z.of_N w <= 2 ^ 64 ->
  cellw SEGS M' a w v.
Proof using SEGS.
  intros M M' a w v [Hv Hr] Hag Ha Haw. split; [exact Hv|].
  rewrite <- Hr. apply rdn_ext; rewrite u64_of_Z, ?N_nat_Z by lia; [lia|].
  intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x).
  replace (bv_unsigned x) with (a + (bv_unsigned x - a)) by lia. apply Hag. lia.
Qed.

Lemma defined_agree : forall M M' a n,
  defined M a n -> agree_on M M' a n -> defined M' a n.
Proof using. intros M M' a n Hd Hag i Hi. rewrite (Hag i Hi). apply Hd. exact Hi. Qed.

Lemma cellw_store : forall M a (w : N) v,
  0 <= v < 2 ^ (8 * Z.of_N w) -> 0 <= a < 2 ^ 64 -> a + Z.of_N w <= 2 ^ 64 -> (w <= 8)%N ->
  cellw SEGS (wbytes M (Z_to_bv 64 a) (word_to_le_bytes (N.to_nat w) (Z_to_bv 64 v))) a w v.
Proof using SEGS.
  intros M a w v Hv Ha Haw Hw. split; [exact Hv|].
  rewrite <- (length_N_to_le_bytes (N.to_nat w) (Z_to_bv 64 v)) at 2.
  apply rdn_wbytes_hit. rewrite length_N_to_le_bytes, u64_of_Z by lia. rewrite N_nat_Z. lia.
Qed.

Lemma agree_on_wbytes_out : forall M (d : word) bs a n,
  bv_unsigned d + Z.of_nat (length bs) <= 2 ^ 64 -> 0 <= a < 2 ^ 64 -> a + n <= 2 ^ 64 ->
  apart (bv_unsigned d) (Z.of_nat (length bs)) a n ->
  agree_on M (wbytes M d bs) a n.
Proof using.
  intros M d bs a n Hd Ha Han Hap i Hi. apply wbytes_outside; [exact Hd|].
  rewrite u64_of_Z by lia. unfold apart in Hap. lia.
Qed.

Lemma defined_wbytes : forall M (d : word) bs a n,
  defined M a n -> defined (wbytes M d bs) a n.
Proof using. intros M d bs a n Hd i Hi. apply wbytes_grows. apply Hd. exact Hi. Qed.

Variable L : Layout.
Variable MI : MallocIface SEGS L.

Section PerTable.
  Variable NS : Z.
  Variable V : Type.
  Variable nval : mem -> Z -> V -> Prop.

  Hypothesis nval_agree : forall M M' p v, nval M p v -> agree_on M M' (p + 20) (NS - 20) -> 0 < p -> p + NS <= 2 ^ 47 -> nval M' p v.
  Hypothesis HNS : 24 <= NS.

  Lemma chain_agree : forall M M' (ents : list (Z * (Z * V))),
    chain SEGS M ents ->
    (forall p k v, In (p, (k, v)) ents -> agree_on M M' p 8 /\ 0 <= p /\ p + 8 <= 2 ^ 64) ->
    chain SEGS M' ents.
  Proof using SEGS V.
    intros M M' ents. induction ents as [|[p [k v]] rest IH]; intros Hc Hag; cbn in *; [exact I|].
    destruct Hc as [Hcell Hrest]. split.
    - destruct (Hag p k v (or_introl eq_refl)) as (Ha & Hp0 & Hp1). eapply cellw_agree; [exact Hcell | exact Ha | lia | cbn; lia].
    - apply IH; [exact Hrest|]. intros p' k' v' Hin. apply (Hag p' k' v'). right. exact Hin.
  Qed.

  Lemma umapx_agree : forall (A A' : AS MI) M M' obj bl bc (ents : list (Z * (Z * V))),
    umapx MI NS nval A M obj bl bc ents ->
    (forall a, umap_foot NS obj bl bc ents a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    (forall p n, In (p, n) (umap_blocks NS bl bc ents) -> In (p, n) (live MI A) -> In (p, n) (live MI A')) ->
    umapx MI NS nval A' M' obj bl bc ents.
  Proof using AC SEGS L MI NS V nval nval_agree HNS.
    intros A A' M M' obj bl bc ents U Hm Hl.
    destruct U as [HD Hoal Holo Hohi Hbseq Hload Hblive Hblal Hbllo Hblhi Hblobj Hbkt Hnd Hch Hnode Hapart].
    assert (Hobj : agree_on M M' obj 40).
    { intros i Hi. apply Hm. left. lia. }
    assert (Hbl : bc <> 0 -> agree_on M M' bl (8 * bc)).
    { intros Hbc i Hi. apply Hm. right; left. split; [exact Hbc | lia]. }
    assert (Hnd_ag : forall p k v, In (p, (k, v)) ents -> agree_on M M' p NS).
    { intros p k v Hin i Hi. apply Hm. right; right. exists p. split; [|lia].
      apply in_map_iff. exists (p, (k, v)). split; [reflexivity | exact Hin]. }
    destruct HD as [Hb Hc Hfst Hsz Hmlf Hdef].
    constructor; try assumption.
    - constructor.
      + eapply cellw_agree; [exact Hb | eapply agree_on_sub; [exact Hobj| lia | cbn; lia] | lia | cbn; lia].
      + eapply cellw_agree; [exact Hc | eapply agree_on_sub; [exact Hobj| lia | cbn; lia] | lia | cbn; lia].
      + eapply cellw_agree; [exact Hfst | eapply agree_on_sub; [exact Hobj| lia | cbn; lia] | lia | cbn; lia].
      + eapply cellw_agree; [exact Hsz | eapply agree_on_sub; [exact Hobj| lia | cbn; lia] | lia | cbn; lia].
      + eapply cellw_agree; [exact Hmlf | eapply agree_on_sub; [exact Hobj| lia | cbn; lia] | lia | cbn; lia].
      + eapply defined_agree; [exact Hdef | exact Hobj].
    - destruct Hblive as [[Hbc0 Hbl0] | [Hbc1 Hin]]; [left; split; assumption | right].
      split; [exact Hbc1|]. apply Hl; [|exact Hin]. unfold umap_blocks.
      destruct (Z.eqb_spec bc 0); [lia|]. apply in_app_iff. left. left. reflexivity.
    - intros i Hi. destruct (Hbkt i Hi) as (b & Hcell & Hok). exists b. split; [|exact Hok].
      assert (bc <> 0) by lia.
      eapply cellw_agree; [exact Hcell | | lia | cbn; lia].
      eapply agree_on_sub; [apply Hbl; lia | lia | cbn; lia].
    - eapply chain_agree; [exact Hch|]. intros p k v Hin.
      destruct (Hnode p k v Hin) as (Hlv & Hp0 & Hp1 & _).
      split; [|lia]. eapply agree_on_sub; [eapply Hnd_ag; exact Hin | lia | lia].
    - intros p k v Hin. destruct (Hnode p k v Hin) as (Hlv & Hp0 & Hp1 & Hal & Hh & Hk & Hkr & Hv & Hap1 & Hap2).
      pose proof (Hnd_ag p k v Hin) as Hag.
      split; [|split; [exact Hp0|split; [exact Hp1|split; [exact Hal|split; [|split; [|split; [exact Hkr|split; [|split; assumption]]]]]]]].
      + apply Hl; [|exact Hlv]. unfold umap_blocks. apply in_app_iff. right.
        apply in_map_iff. exists (p, (k, v)). split; [reflexivity | exact Hin].
      + eapply cellw_agree; [exact Hh | eapply agree_on_sub; [exact Hag | lia | cbn; lia] | lia | cbn; lia].
      + eapply cellw_agree; [exact Hk | eapply agree_on_sub; [exact Hag | lia | cbn; lia] | lia | cbn; lia].
      + eapply nval_agree; [exact Hv | eapply agree_on_sub; [exact Hag | lia | lia] | lia | lia].
  Qed.

  Lemma umapx_empty : forall (A : AS MI) M obj,
    cell8 SEGS M obj 0 -> cell8 SEGS M (obj + 8) 0 -> cell8 SEGS M (obj + 16) 0 -> cell8 SEGS M (obj + 24) 0 ->
    cell4 SEGS M (obj + 32) 0x3f800000 -> defined M obj 40 ->
    obj mod 8 = 0 -> 0 < obj -> obj + 40 <= 2 ^ 47 ->
    umapx MI NS nval A M obj 0 0 [].
  Proof using AC SEGS L MI NS V nval.
    intros A M obj H0 H8 H16 H24 H32 Hdef Hal Hlo Hhi.
    constructor.
    all: first [ assumption | constructor; assumption | (cbn; lia) | (cbn; left; reflexivity)
               | (left; split; reflexivity) | reflexivity | (intros _; unfold apart; lia)
               | (intros i Hi; exfalso; lia) | exact I | (intros p k v []) | (intros p q [] _) | constructor ].
  Qed.
End PerTable.

Lemma nval24_agree : forall M M' p v, nval24 SEGS M p v -> agree_on M M' (p + 20) (24 - 20) -> 0 < p -> p + 24 <= 2 ^ 47 ->
  nval24 SEGS M' p v.
Proof using SEGS. intros M M' p v H Hag Hp0 Hp1. eapply cellw_agree; [exact H | exact Hag | lia | cbn; lia]. Qed.

Lemma nval32_agree : forall M M' p v, nval32 SEGS M p v -> agree_on M M' (p + 20) (32 - 20) -> 0 < p -> p + 32 <= 2 ^ 47 ->
  nval32 SEGS M' p v.
Proof using SEGS.
  intros M M' p [[t w] e] (Ht & Hw & He) Hag Hp0 Hp1. cbn. split; [|split].
  - eapply cellw_agree; [exact Ht | eapply agree_on_sub; [exact Hag|lia|lia] | lia | cbn; lia].
  - eapply cellw_agree; [exact Hw | eapply agree_on_sub; [exact Hag|lia|lia] | lia | cbn; lia].
  - eapply cellw_agree; [exact He | eapply agree_on_sub; [exact Hag|lia|lia] | lia | cbn; lia].
Qed.

End Facts.
