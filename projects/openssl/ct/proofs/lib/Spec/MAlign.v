(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import STree Malloc MallocCtrl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition set_size_m (p e : aptr) (n b3 : Z) (st : mstate) : mstate :=
  let res := snd e - snd p - n in
  let st1 := if negb (res =? 0) then wr8 (aadd e (- res)) 0 st else st in
  let '(st2, r) := if 5 <=? res then (wr32 (aadd e (-4)) res (wr8 (aadd e (-5)) 0 st1), 5) else (st1, res) in
  wr8 (aadd p (-3)) (Z.land b3 31 + Z.shiftl r 5) st2.

Definition realign_at (st : mstate) (g : aptr) (idx n off adj : Z) : mstate * aptr :=
  let mr := get_meta_rec st g in
  let stride := get_stride mr in
  let gm := default (0%N, 0) (m_mem mr) in
  let c := aadd gm (UNIT + stride * idx) in
  let e := aadd c (stride - IB) in
  let p0 := aadd c (UNIT * off) in
  if adj =? 0 then (set_size_m p0 e n idx st, p0)
  else
    let p := aadd p0 adj in
    let st1 := wr8 (aadd p (-4)) 0 st in
    let st2 := wr8 (aadd p (-3)) idx st1 in
    let st3 := wr16 (aadd p (-2)) ((snd p - (snd gm + UNIT)) / UNIT) st2 in
    let st4 := set_size_m p e n idx st3 in
    let st5 := wr8 (aadd c (-3)) 224 st4 in
    (wr16 (aadd c (-2)) ((snd p - snd c) / UNIT) st5, p).

Definition realign (st : mstate) (c : cptr) (off n adj : Z) : mstate :=
  match s_slots st !! c with
  | Some (g, idx) => fst (realign_at st g idx n off adj)
  | None => st
  end.

Lemma strip_set_size_m p e n b st : strip (set_size_m p e n b st) = strip st.
Proof. unfold set_size_m. destruct (5 <=? _); destruct (negb _); reflexivity. Qed.

Lemma strip_realign_at st g idx n off adj : strip (fst (realign_at st g idx n off adj)) = strip st.
Proof.
  unfold realign_at. destruct (adj =? 0); cbn -[set_size_m wr8 wr16 strip]; rewrite ?strip_wr16, ?strip_wr8, strip_set_size_m; reflexivity.
Qed.

Lemma strip_realign st c off n adj : strip (realign st c off n adj) = strip st.
Proof. unfold realign. destruct (s_slots st !! c) as [[g idx]|]; [apply strip_realign_at| reflexivity]. Qed.

Lemma realign_snd st g idx n off adj :
  snd (realign_at st g idx n off adj)
  = aadd (aadd (default (0%N, 0) (m_mem (get_meta_rec st g))) (UNIT + get_stride (get_meta_rec st g) * idx)) (UNIT * off + (if adj =? 0 then 0 else adj)).
Proof.
  unfold realign_at. destruct (adj =? 0); cbn -[set_size_m wr8 wr16 Z.add Z.mul]; unfold aadd; cbn [fst snd]; f_equal; lia.
Qed.

(* [comment removed for export] *)
Lemma s_tick_wr8 p v st : s_tick (wr8 p v st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_tick_wr16 p v st : s_tick (wr16 p v st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_tick_wr32 p v st : s_tick (wr32 p v st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_tick_set_size_m p e n b st : s_tick (set_size_m p e n b st) = s_tick st.
Proof. unfold set_size_m. destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma s_tick_realign_at st g idx n off adj : s_tick (fst (realign_at st g idx n off adj)) = s_tick st.
Proof.
  unfold realign_at. destruct (adj =? 0); cbn -[set_size_m wr8 wr16 s_tick]; rewrite ?s_tick_wr16, ?s_tick_wr8, s_tick_set_size_m; reflexivity.
Qed.
Lemma s_tick_realign st c off n adj : s_tick (realign st c off n adj) = s_tick st.
Proof. unfold realign. destruct (s_slots st !! c) as [[g idx]|]; [apply s_tick_realign_at| reflexivity]. Qed.
