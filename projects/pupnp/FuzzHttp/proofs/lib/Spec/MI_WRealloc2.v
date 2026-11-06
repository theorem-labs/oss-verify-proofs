(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl KLedger MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom.
Import ListNotations.
Local Open Scope Z_scope.

Section SEP.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

#[using="X L BL LS INV IM IS"] Lemma blk_slot_geom c mm i : s_slots st !! c = Some (mm, i) ->
  exists bm, hosts st bm mm /\ 0 <= i <= m_last_idx (MR st mm) /\ c = (fst bm, sstart (MR st mm) i).
Proof.
  intros Hs. destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bm Hbm] & Hi & Ec).
  exists bm. split; [exact Hbm|]. split; [exact Hi|]. rewrite Ec. apply (slot_start'_eq _ _ _ IM). exact Hbm.
Qed.

#[using="X L BL LS INV IM IG IS"] Lemma blk_slots_sep c mm i c' mm' i' :
  s_slots st !! c = Some (mm, i) -> s_groups st !! c = None ->
  s_slots st !! c' = Some (mm', i') -> s_groups st !! c' = None ->
  c' <> c -> fst c' = fst c ->
  snd c' + get_stride (MR st mm') <= snd c \/ snd c + get_stride (MR st mm) <= snd c'.
Proof.
  intros Hs NH Hs' NH' NE Hf.
  destruct (blk_slot_geom c mm i Hs) as (bm & Hbm & Hi & Ec).
  destruct (blk_slot_geom c' mm' i' Hs') as (bm' & Hbm' & Hi' & Ec').
  rewrite Ec in NH. rewrite Ec' in NH'.
  assert (Hfb : fst bm' = fst bm) by (rewrite Ec, Ec' in Hf; exact Hf).
  assert (NE2 : mm' <> mm \/ i' <> i).
  { destruct (aptr_eq_dec mm' mm) as [->|]; [| left; assumption]. right. intros ->. apply NE. rewrite Ec, Ec', Hfb. reflexivity. }
  destruct (sep_ext X st BL LS IM IG IS mm bm i Hbm Hi NH mm' bm' i' Hbm' Hfb Hi' NE2 NH') as [A|A];
    rewrite sstart_succ in A; rewrite Ec, Ec'; cbn [snd]; [left| right]; exact A.
Qed.

#[using="X L BL LS INV IM IG IS"] Lemma blk_slot_nogrp c mm i b' gh :
  s_slots st !! c = Some (mm, i) -> s_groups st !! c = None ->
  s_groups st !! b' = Some gh -> fst b' = fst c ->
  snd b' + 16 <= snd c \/ snd c + get_stride (MR st mm) <= snd b' + 4.
Proof.
  intros Hs NH Hb' Hf.
  destruct (blk_slot_geom c mm i Hs) as (bm & Hbm & Hi & Ec). rewrite Ec in NH.
  destruct gh as [[m2|] ai2]; [| exfalso; exact (ig_nometa _ _ _ IG _ _ Hb')].
  assert (H2 : hosts st b' m2) by (exists ai2; exact Hb').
  assert (Hfb : fst b' = fst bm) by (rewrite Ec in Hf; exact Hf).
  destruct (sep_ghdr X st BL LS IM IG IS mm bm i Hbm Hi NH m2 b' H2 Hfb) as [A|A];
    rewrite ?sstart_succ in A; rewrite Ec; cbn [snd]; [left| right]; exact A.
Qed.
End SEP.
