(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition inflate_fast_frame_stmt : Prop :=
  forall (s : inflate_state) (c : icall) (r : iregs),
    let w1 := inflate_fast (mkW s c r) in
    ic_next_out c <= ic_next_out (w_c w1)
    /\ arr_len (ic_outbuf (w_c w1)) = arr_len (ic_outbuf c)
    /\ (forall i, (i < ic_next_out c \/ ic_next_out (w_c w1) <= i) ->
          arr_get (ic_outbuf (w_c w1)) i = arr_get (ic_outbuf c) i).
