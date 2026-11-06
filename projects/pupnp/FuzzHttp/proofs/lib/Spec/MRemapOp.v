(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl KLedger KRemapDef MI_Inv MI_WGroup MI_WRealloc.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Export KRemapDef.
Import ListNotations.
Local Open Scope Z_scope.

Definition shadow_cut (M : Z) (r : shadow) : shadow :=
  mkShadow (filter (fun kv : Z * (Z * N) => kv.1 <? M) (r_cells r)) (r_hav r) (r_havp r).

Definition rebase_st (st : mstate) (rid : N) (g : aptr) (dst nn on : Z) : mstate :=
  wr8 (rid, nn - 4) 0 (upd_shadow rid (shadow_cut (Z.min on nn)) (rebase_ctrl st rid g dst nn)).

Definition mremap_needed (off n' : Z) : Z := round_up_pg (n' + UNIT * off + UNIT + IB).

Definition mremap_full (st : mstate) (c : cptr) (off n n' dst : Z) : mstate :=
  match (s_slots st) !! c with
  | Some (g, i) =>
      let on := m_maplen (get_meta_rec st g) * 4096 in
      let nn := mremap_needed off n' in
      let st1 := set_tick (N.succ (s_tick st)) st in
      let st2 := rebase_st st1 (fst c) g dst nn on in
      let p := aadd c (UNIT * off) in
      let e := aadd c (nn - UNIT - IB) in
      let b3 := i + 32 * Z.min (get_stride (get_meta_rec st g) - IB - UNIT * off - n) 5 in
      havoc p n' (wrs (ss_list p e n' b3) st2)
  | None => st
  end.

Lemma strip_upd_shadow rid f st : strip (upd_shadow rid f st) = strip st.
Proof. reflexivity. Qed.
Lemma strip_rebase_ctrl st rid g dst nn : strip (rebase_ctrl st rid g dst nn) = rebase_ctrl (strip st) rid g dst nn.
Proof. reflexivity. Qed.
Lemma strip_rebase_st st rid g dst nn on : strip (rebase_st st rid g dst nn on) = cremap (strip st) rid g dst nn.
Proof. unfold rebase_st. rewrite strip_wr8, strip_upd_shadow. apply strip_rebase_ctrl. Qed.

Lemma strip_mremap_full st c off n n' dst g i :
  s_slots st !! c = Some (g, i) ->
  strip (mremap_full st c off n n' dst) = cremap (strip st) (fst c) g dst (mremap_needed off n').
Proof.
  intros Hs. unfold mremap_full. rewrite Hs. rewrite strip_havoc, strip_wrs, strip_rebase_st, strip_set_tick. reflexivity.
Qed.
