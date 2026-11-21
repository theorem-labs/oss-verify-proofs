(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ISLayout.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Set Implicit Arguments.
Unset Implicit Arguments.


Definition ffx_of (s : inflate_state) (c : icall) (r : iregs) : ffx :=
  mkFX (ic_input c) (ic_next_in c + wrap32 (ic_avail_in c - 5))
       (ic_next_out c - wrap32 (ir_out r - ic_avail_out c))
       (ic_next_out c + wrap32 (ic_avail_out c - 257))
       (is_wsize s) (is_whave s) (is_wnext s) (is_window s)
       (zmask (is_lenbits s)) (zmask (is_distbits s)) (is_sane s).
Definition ff0_of (s : inflate_state) (c : icall) : ffs :=
  mkF (ic_next_in c) (ic_next_out c) (is_hold s) (is_bits s) 0 0 0 (FOut 0) (ic_outbuf c).

Definition ctab_len (p : codeptr) : Z :=
  match p with CDyn ofs => 1444 - ofs | CLenfix => 512 | CDistfix => 32 end.

Definition x_begm (c : icall) (r : iregs) : Z := ic_next_out c - szwrap 32 (ir_out r - ic_avail_out c).

Definition faddr (WB P0 : Z) (fr : fromptr) : Z := match fr with FWin i => WB + i | FOut i => P0 + i end.
Definition src_ok (WN bnd : Z) (fr : fromptr) : Prop := match fr with FWin i => 0 <= i < WN | FOut i => 0 <= i < bnd end.

Lemma faddr_succ : forall WB P0 fr, faddr WB P0 (from_succ fr) = faddr WB P0 fr + 1.
Proof. intros WB P0 [i|i]; cbn; lia. Qed.
Lemma faddr_add : forall WB P0 k fr, faddr WB P0 (fr_add fr k) = faddr WB P0 fr + Z.of_nat k.
Proof.
  intros WB P0 k. induction k as [|k IH]; intros fr; [cbn; lia|].
  cbn [fr_add]. rewrite IH, faddr_succ. lia.
Qed.

Definition FF0 (sp : Z) : franges := [(sp, 112)].
Definition FF1 (sp P0 ON : Z) : franges := [(sp, 112); (P0, ON)].
Definition FFall (sp P0 ON ZP S : Z) : franges :=
  [(sp, 112); (P0, ON); (ZP, 12); (ZP + 24, 12); (ZP + 48, 8); (S + 8, 4); (S + 80, 12)].

Section Facts.

End Facts.
