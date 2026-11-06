(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_WFree.
From OSSVerify.Proofs.openssl.pem.lib.Malloc Require Import MallocRep MallocTree MallocBlocks MallocFacts_B MallocFacts_inv MallocFacts_inv2.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling}.
Lemma areach_blk_span : forall {resv} st LB (blk : block) g i,
  AREACH_from resv st LB -> In blk LB -> s_slots st !! blk_slot blk = Some (g, i) ->
  exists r, s_regions st !! (fst (blk_slot blk)) = Some r /\ r_kind r = RKGroup
    /\ forall blk', In blk' LB -> blk_slot blk' <> blk_slot blk -> fst (blk_slot blk') = fst (blk_slot blk) ->
         blk_addr blk' + blk_size blk' <= r_base r + sstart (MR st g) i - 4
         \/ r_base r + sstart (MR st g) (i + 1) - 4 <= blk_addr blk'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros resv st LB blk g i AR Hblk Hs.
  destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & _ & _ & _ & CR).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (LB_geo _ _ _ _ _ INV _ CR _ Hblk) as (c & off & n & m & bm & i0 & r & Hk & C1 & C2 & Hm & Hi & Ec & NH & Hr & Kr & Ea & Ho & Hn & Fit).
  assert (E : m = g /\ i0 = i).
  { pose proof (is_total _ _ _ IS _ _ _ Hm Hi) as T.
    rewrite (slot_start'_eq _ _ _ IM _ _ _ Hm), <- Ec, <- C1, Hs in T. inversion T. split; reflexivity. }
  destruct E as [-> ->].
  exists r. rewrite C1, Ec. cbn [fst]. split; [exact Hr|]. split; [exact Kr|].
  intros blk' Hblk' NE Hf.
  destruct (LB_geo _ _ _ _ _ INV _ CR _ Hblk') as (c2 & o2 & n2 & m2 & bm2 & i2 & r2 & K2 & D1 & D2 & Hm2 & Hi2 & Ec2 & N2 & R2 & _ & A2 & O2 & P2 & F2).
  rewrite D1, Ec2 in Hf. cbn [fst] in Hf. rewrite Hf, Hr in R2. inversion R2; subst r2.
  rewrite A2, D2. pose proof (sstart_succ st m2 i2) as SS2.
  assert (NE' : m2 <> g \/ i2 <> i). { destruct (aptr_eq_dec m2 g) as [->|]; [right| now left]. intros ->. apply NE. rewrite D1, Ec2, Hf. reflexivity. }
  rewrite Ec in NH. rewrite Ec2 in N2.
  destruct (sep_ext _ _ _ _ IM IG IS g bm i Hm Hi NH m2 bm2 i2 Hm2 Hf Hi2 NE' N2) as [A|A]; unfold UNIT, IB in *; lia.
Qed.
End WithCeiling0.
