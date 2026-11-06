(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Monad STree Malloc MallocCtrl Stdio Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Definition MREMAP_MAYMOVE : Z := 1.

(* [comment removed for export] *)
Definition rr_needed (n base : Z) : Z := Z.land (n + base + UNIT + IB + 4095) (-4096).

(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive rplan : Type :=
| RPInPlace                                          (* [comment removed for export] *)
| RPRemap (rid : N) (g : aptr) (base on nn : Z)      (* [comment removed for export] *)
| RPFallback                                         (* [comment removed for export] *)
| RPUndef.                                           (* [comment removed for export] *)

Definition rplan_of (cs : mstate) (c : cptr) (A n : Z) : rplan :=
  match (s_slots cs) !! c with
  | None => RPUndef
  | Some (g, idx) =>
    let mr := get_meta_rec cs g in
    let base := A - conc cs c in                       (* [comment removed for export] *)
    let avail := get_stride mr - IB - base in          (* [comment removed for export] *)
    if (n <=? avail) && (n <? MMAP_THRESHOLD) && (m_sizeclass mr <=? size_to_class n + 1) then RPInPlace
    else if (48 <=? m_sizeclass mr) && (MMAP_THRESHOLD <=? n) then
      if negb (m_sizeclass mr =? 63) then RPUndef else
      match m_mem mr with
      | Some b => RPRemap (fst b) g (conc cs b) (m_maplen mr * 4096) (rr_needed n base)
      | None => RPUndef
      end
    else RPFallback
  end.

(* [comment removed for export] *)
Definition cs_remap (cs : mstate) (rid : N) (g : aptr) (d nn : Z) : mstate :=
  upd_meta g (m_set_maplen (nn / 4096)) (upd_region rid (fun r => mkRegion (r_kind r) d nn) cs).

(* [comment removed for export] *)
Definition remap_grow_ok (cs : mstate) (base on nn : Z) : bool :=
  (nn <=? on) || ((base + nn <=? alloc_ceiling) && ranges_free (live_ranges cs) (base + on) (nn - on)).
Definition remap_move_ok (cs : mstate) (nn d : Z) : bool :=
  (0 <? d) && (d mod PGSZ =? 0) && (d + nn <=? alloc_ceiling) && ranges_free (live_ranges cs) d nn.

Definition rr_fallback (p : bptr) (n : Z) : Monad.M PState (option bptr) :=
  q <- raw_malloc n ;;
  match q with
  | None => mret None
  | Some q => raw_free p ;;; mret (Some q)
  end.

(* [comment removed for export] *)
Definition raw_realloc (p : bptr) (A n : Z) : Monad.M PState (option bptr) :=
  s <- mget ;;
  match rplan_of (ps_m s) (fst p) A n with
  | RPUndef => munr
  | RPInPlace => mret (Some p)
  | RPRemap rid g base on nn =>
      if on =? nn then mret (Some p) else
      a <- msys (NMremap base on nn MREMAP_MAYMOVE) (dec_mremap base on nn []) ;;
      match a with
      | MrErr _ => rr_fallback p n
      | MrInPlace =>
          if remap_grow_ok (ps_m s) base on nn
          then mupd (set_m (cs_remap (ps_m s) rid g base nn)) ;;; mret (Some p)
          else munr
      | MrMoved d =>
          if remap_move_ok (ps_m s) nn d
          then mupd (set_m (cs_remap (ps_m s) rid g d nn)) ;;; mret (Some p)
          else munr
      end
  | RPFallback => rr_fallback p n
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition set_size_i (p e : aptr) (n idx : Z) (st : mstate) : mstate :=
  let reserved := snd e - snd p - n in
  let st1 := if negb (reserved =? 0) then wr8 (aadd e (- reserved)) 0 st else st in
  let '(st2, reserved) :=
    if 5 <=? reserved then (wr8 (aadd e (-5)) 0 (wr32 (aadd e (-4)) reserved st1), 5)
    else (st1, reserved) in
  wr8 (aadd p (-3)) (idx + Z.shiftl reserved 5) st2.

(* [comment removed for export] *)
Definition rr_inplace_full (st : mstate) (c : cptr) (up : aptr) (n : Z) : mstate :=
  match (s_slots st) !! c with
  | None => st
  | Some (g, idx) =>
    let mr := get_meta_rec st g in
    let e := aadd c (get_stride mr - IB) in
    let st1 := set_tick (N.succ (s_tick st)) st in
    havoc up n (set_size_i up e n idx st1)
  end.

(* [comment removed for export] *)
Definition prune_shadow (rid : N) (len : Z) (st : mstate) : mstate :=
  upd_shadow rid (fun sh =>
    mkShadow (filter (fun kv => fst kv <? len) (r_cells sh))
             (filter (fun kv => 16 * fst kv <? len) (r_hav sh))
             (filter (fun kv => 4096 * fst kv <? len) (r_havp sh))) st.

(* [comment removed for export] *)
Definition rr_remap_full (st : mstate) (c : cptr) (up : aptr) (n : Z) (d nn : Z) : mstate :=
  match (s_slots st) !! c with
  | None => st
  | Some (g, idx) =>
    let mr := get_meta_rec st g in
    let rid := fst c in
    let on := m_maplen mr * 4096 in
    let b := default (rid, 0) (m_mem mr) in
    let e := aadd b (nn - IB) in
    let st1 := set_tick (N.succ (s_tick st)) st in
    let st2 := upd_region rid (fun r => mkRegion (r_kind r) d nn) st1 in
    let st3 := prune_shadow rid (Z.min on nn) st2 in
    let st4 := upd_meta g (m_set_maplen (nn / 4096)) st3 in
    havoc up n (set_size_i up e n idx (wr8 e 0 st4))
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma strip_set_tick' v st : strip (set_tick v st) = strip st.
Proof. reflexivity. Qed.
Lemma strip_upd_shadow rid f st : strip (upd_shadow rid f st) = strip st.
Proof. reflexivity. Qed.
Lemma strip_wr8 p v st : strip (wr8 p v st) = strip st.
Proof. reflexivity. Qed.
Lemma strip_wr32 p v st : strip (wr32 p v st) = strip st.
Proof. reflexivity. Qed.
Lemma strip_havoc p n st : strip (havoc p n st) = strip st.
Proof. unfold havoc. destruct (n <=? 0); reflexivity. Qed.
Lemma strip_prune rid len st : strip (prune_shadow rid len st) = strip st.
Proof. reflexivity. Qed.
Lemma strip_set_size_i p e n idx st : strip (set_size_i p e n idx st) = strip st.
Proof.
  unfold set_size_i. destruct (5 <=? snd e - snd p - n); destruct (negb (snd e - snd p - n =? 0)); reflexivity.
Qed.
Lemma s_slots_strip st : s_slots (strip st) = s_slots st.
Proof. reflexivity. Qed.
Lemma get_meta_rec_strip st g : get_meta_rec (strip st) g = get_meta_rec st g.
Proof. reflexivity. Qed.
Lemma conc_strip st q : conc (strip st) q = conc st q.
Proof. reflexivity. Qed.
Lemma live_ranges_strip st : live_ranges (strip st) = live_ranges st.
Proof. reflexivity. Qed.

Lemma strip_rr_inplace_full st c up n : strip (rr_inplace_full st c up n) = strip st.
Proof.
  unfold rr_inplace_full. destruct (s_slots st !! c) as [[g idx]|]; [|reflexivity].
  rewrite strip_havoc, strip_set_size_i. reflexivity.
Qed.

Lemma strip_upd_region rid f st : strip (upd_region rid f st) = upd_region rid f (strip st).
Proof. unfold upd_region, get_region. cbn. destruct (s_regions st !! rid); reflexivity. Qed.
Lemma strip_upd_meta g f st : strip (upd_meta g f st) = upd_meta g f (strip st).
Proof. reflexivity. Qed.

Lemma strip_rr_remap_full st c up n d nn :
  strip (rr_remap_full st c up n d nn) =
  match (s_slots st) !! c with
  | None => strip st
  | Some (g, idx) => cs_remap (strip st) (fst c) g d nn
  end.
Proof.
  unfold rr_remap_full, cs_remap. destruct (s_slots st !! c) as [[g idx]|]; [|reflexivity].
  rewrite strip_havoc, strip_set_size_i, strip_wr8, strip_upd_meta, strip_prune, strip_upd_region, strip_set_tick'.
  reflexivity.
Qed.

Lemma rplan_of_strip st c A n : rplan_of (strip st) c A n = rplan_of st c A n.
Proof. reflexivity. Qed.


End CeilWrap.
