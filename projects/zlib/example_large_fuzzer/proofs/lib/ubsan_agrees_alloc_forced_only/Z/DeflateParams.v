(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Deflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition cfunc_id (level : Z) : Z :=
  if Z.eqb level 0 then 0 else if Z.leb level 3 then 1 else 2.

(* [comment removed for export] *)
Definition dparams_set_level (s : deflate_state) (level : Z) : deflate_state :=
  let s :=
    if Z.eqb (ds_level s) 0 && negb (Z.eqb (ds_matches s) 0) then
      let s := if Z.eqb (ds_matches s) 1 then slide_hash s else clear_hash s in
      set_matches s 0
    else s in
  let s := set_level s level in
  let '(good, lazy, nice, chain) := configuration_table level in
  let s := set_max_lazy_match s lazy in
  let s := set_good_match s good in
  let s := set_nice_match s nice in
  set_max_chain_length s chain.

(* [comment removed for export] *)
Definition deflateParams_core (s : deflate_state) (level strategy : Z) : deflate_state * Z :=
  if deflateStateCheck s then (s, Z_STREAM_ERROR)
  else
    let level := if Z.eqb level Z_DEFAULT_COMPRESSION then 6 else level in
    if (level <? 0) || (9 <? level) || (strategy <? 0) || (Z_FIXED <? strategy) then (s, Z_STREAM_ERROR)
    else
      (* [comment removed for export] *)
      let '(s, r) :=
        if (negb (Z.eqb strategy (ds_strategy s)) || negb (Z.eqb (cfunc_id (ds_level s)) (cfunc_id level)))
           && negb (Z.eqb (ds_last_flush s) (-2))
        then
          let '(s, err) := deflate_core s Z_BLOCK in
          if Z.eqb err Z_STREAM_ERROR then (s, Some err)
          else if negb (Z.eqb (cs_avail_in (ds_strm s)) 0)
                  || negb (Z.eqb ((ds_strstart s - ds_block_start s) + ds_lookahead s) 0)
          then (s, Some Z_BUF_ERROR)
          else (s, None)
        else (s, None) in
      match r with
      | Some rc => (s, rc)
      | None =>
          let s := if negb (Z.eqb (ds_level s) level) then dparams_set_level s level else s in
          (set_strategy s strategy, Z_OK)
      end.

(* [comment removed for export] *)
Definition deflateParams_m (s : deflate_state) (zc : ZCall) (level strategy : Z) : deflate_state * ZRet :=
  let s := set_strm s (cstrm_of_call zc) in
  let '(s, rc) := deflateParams_core s level strategy in
  (s, zret_of_cs (ds_strm s) rc).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cfunc_id_0 : cfunc_id 0 = 0. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition dparams_flushes (s : deflate_state) (level strategy : Z) : bool :=
  (negb (Z.eqb strategy (ds_strategy s)) || negb (Z.eqb (cfunc_id (ds_level s)) (cfunc_id level)))
  && negb (Z.eqb (ds_last_flush s) (-2)).

Lemma deflateParams_core_eq : forall s level strategy,
  deflateStateCheck s = false ->
  0 <= level <= 9 -> 0 <= strategy <= Z_FIXED ->
  deflateParams_core s level strategy =
    (let '(s1, r) :=
       if dparams_flushes s level strategy then
         let '(s1, err) := deflate_core s Z_BLOCK in
         if Z.eqb err Z_STREAM_ERROR then (s1, Some err)
         else if negb (Z.eqb (cs_avail_in (ds_strm s1)) 0) || negb (Z.eqb ((ds_strstart s1 - ds_block_start s1) + ds_lookahead s1) 0)
              then (s1, Some Z_BUF_ERROR) else (s1, None)
       else (s, None) in
     match r with
     | Some rc => (s1, rc)
     | None => (set_strategy (if negb (Z.eqb (ds_level s1) level) then dparams_set_level s1 level else s1) strategy, Z_OK)
     end).
Proof.
  intros s level strategy HC HL HS. unfold deflateParams_core, dparams_flushes. rewrite HC.
  replace (Z.eqb level Z_DEFAULT_COMPRESSION) with false.
  2:{ symmetry. apply Z.eqb_neq. unfold Z_DEFAULT_COMPRESSION. intros E. rewrite E in HL. destruct HL as [HL _]. apply HL. reflexivity. }
  replace ((level <? 0) || (9 <? level) || (strategy <? 0) || (Z_FIXED <? strategy)) with false.
  2:{ symmetry. rewrite !Bool.orb_false_iff. unfold Z_FIXED in *. repeat split; apply Z.ltb_ge; lia. }
  reflexivity.
Qed.
