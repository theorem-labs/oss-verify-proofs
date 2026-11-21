(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ModelRel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition fw_slide (s : deflate_state) (wsize : Z) : deflate_state * Z :=
  let more := wrap32 (ds_window_size s - ds_lookahead s - ds_strstart s) in
  if Z.leb (wsize + (ds_w_size s - MIN_LOOKAHEAD)) (ds_strstart s) then
    let s := set_window s (arr_blit (ds_window s) 0 (ds_window s) wsize (wrap32 (wsize - more))) in
    let s := set_match_start s (wrap32 (ds_match_start s - wsize)) in
    let s := set_strstart s (ds_strstart s - wsize) in
    let s := set_block_start s (ds_block_start s - wsize) in
    let s := if Z.ltb (ds_strstart s) (ds_insert s) then set_insert s (ds_strstart s) else s in
    let s := slide_hash s in
    (s, wrap32 (more + wsize))
  else (s, more).

Definition fw_read (s : deflate_state) (more : Z) : deflate_state * bool :=
  if Z.eqb (cs_avail_in (ds_strm s)) 0 then (s, true)
  else
    let '(s, n) := read_buf s (RB_window (ds_strstart s + ds_lookahead s)) more in
    let s := set_lookahead s (ds_lookahead s + n) in
    let s :=
      if Z.leb MIN_MATCH (ds_lookahead s + ds_insert s) then
        let str := ds_strstart s - ds_insert s in
        let s := set_ins_h s (arr_get (ds_window s) str) in
        let s := set_ins_h s (update_hash s (ds_ins_h s) (arr_get (ds_window s) (str + 1))) in
        fill_window_insert (Z.to_nat (ds_insert s)) s str
      else s in
    (s, false).

Definition sd_prep (s : deflate_state) (wrap : Z) (dictionary : list Z) : deflate_state * list Z :=
  let dictLength := zlength dictionary in
  let s := if Z.eqb wrap 1
           then set_strm s (cset_adler (ds_strm s) (adler32_upd (cs_adler (ds_strm s)) dictionary))
           else s in
  let s := set_wrap s 0 in
  if Z.leb (ds_w_size s) dictLength then
    let s := if Z.eqb wrap 0 then
               let s := clear_hash s in
               let s := set_strstart s 0 in
               let s := set_block_start s 0 in
               set_insert s 0
             else s in
    (s, zskipn (dictLength - ds_w_size s) dictionary)
  else (s, dictionary).

Definition sd_run (s : deflate_state) (dict : list Z) (wrap : Z) : deflate_state :=
  let saved := ds_strm s in
  let s := set_strm s (cset_avail_in (cset_next_in (cset_input saved (arr_of_list dict)) 0) (zlength dict)) in
  let s := fill_window s in
  let s := setdict_outer (Z.to_nat (zlength dict + 2)) s in
  let s := set_strstart s (ds_strstart s + ds_lookahead s) in
  let s := set_block_start s (ds_strstart s) in
  let s := set_insert s (ds_lookahead s) in
  let s := set_lookahead s 0 in
  let s := set_prev_length s (MIN_MATCH - 1) in
  let s := set_match_length s (MIN_MATCH - 1) in
  let s := set_match_available s 0 in
  let st := ds_strm s in
  let st := cset_input (cset_next_in (cset_avail_in st (cs_avail_in saved)) (cs_next_in saved)) (cs_input saved) in
  let s := set_strm s st in
  set_wrap s wrap.

Section Init.
  Context {St : Type}.
  Variable hooks : zhooks St.

  Ltac mhnf := lazymatch goal with |- mall ?P ?tg => let t' := eval hnf in tg in change (mall P t') end.

  Ltac mlet :=
    lazymatch goal with
    | |- mall ?P ((let x := ?E in ?B) ?g) =>
        let T := type of E in let K := constr:(fun x : T => B g) in
        change (mall P (K E)); generalize E; intros ?; cbv beta
    | |- mall ?P (let x := ?E in ?B) =>
        let T := type of E in let K := constr:(fun x : T => B) in
        change (mall P (K E)); generalize E; intros ?; cbv beta
    end.

  Ltac mstep :=
    first [ mlet
          | refine (mall_sbind_any _ _ _ _ _); intros ? ?
          | lazymatch goal with
            | |- mall _ (mbind _ _) => refine (mall_bind (fun _ => True) _ _ _ (mall_true _) _); intros ? _
            | |- mall _ ((if ?c then _ else _) _) => destruct c eqn:?
            | |- mall _ (if ?c then _ else _) => destruct c eqn:?
            | |- mall _ ((match ?c with _ => _ end) _) => destruct c eqn:?
            | |- mall _ (match ?c with _ => _ end) => destruct c eqn:?
            end
          | progress mhnf ].

End Init.
