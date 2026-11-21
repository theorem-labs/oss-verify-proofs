(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog ZIface DeflateState Trees DeflateLz DeflateBlk Deflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition cfg_func (level : Z) : Z :=
  if Z.eqb level 0 then 0 else if Z.leb level 3 then 1 else 2.

Definition deflateParams_switch (s : deflate_state) (level strategy : Z) : deflate_state :=
  let s :=
    if negb (Z.eqb (ds_level s) level) then
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
      set_max_chain_length s chain
    else s in
  set_strategy s strategy.

Definition deflateParams_core (s : deflate_state) (level strategy : Z) : deflate_state * Z :=
  if deflateStateCheck s then (s, Z_STREAM_ERROR)
  else
    let level := if Z.eqb level Z_DEFAULT_COMPRESSION then 6 else level in
    if (level <? 0) || (9 <? level) || (strategy <? 0) || (Z_FIXED <? strategy)
    then (s, Z_STREAM_ERROR)
    else
      let func := cfg_func (ds_level s) in
      let '(s, r) :=
        if (negb (Z.eqb strategy (ds_strategy s)) || negb (Z.eqb func (cfg_func level)))
           && negb (Z.eqb (ds_last_flush s) (-2))
        then
          let '(s, err) := deflate_core s Z_BLOCK in
          if Z.eqb err Z_STREAM_ERROR then (s, Some err)
          else if negb (Z.eqb (cs_avail_in (ds_strm s)) 0)
                  || negb (Z.eqb (ds_strstart s - ds_block_start s + ds_lookahead s) 0)
          then (s, Some Z_BUF_ERROR)
          else (s, None)
        else (s, None) in
      match r with
      | Some rc => (s, rc)
      | None => (deflateParams_switch s level strategy, Z_OK)
      end.

Definition deflateParams_m (s : deflate_state) (zc : ZCall) (level strategy : Z)
  : deflate_state * ZRet :=
  let s := set_strm s (cstrm_of_call zc) in
  let '(s, rc) := deflateParams_core s level strategy in
  (s, zret_of_cs (ds_strm s) rc).
