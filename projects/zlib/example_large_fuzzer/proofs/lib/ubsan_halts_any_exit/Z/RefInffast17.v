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
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ISLayout.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastSafe.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInffast1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInffast2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInffast3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInffast4.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInffast5.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInffast6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInffast8.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInffast10.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInffast12.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInffast14.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInffast16.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma land_wrap32_zmask : forall h e, 0 <= h -> 0 <= e < 32 -> Z.land (wrap32 h) (zmask e) = h mod 2 ^ e.
Proof.
  intros h e Hh He. rewrite zmask_pow2, land_ones_mod, wrap32_mod by lia.
  apply Z.mod_mod_divide. exists (2 ^ (32 - e)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma land_zmask : forall h e, 0 <= e < 32 -> Z.land h (zmask e) = h mod 2 ^ e.
Proof. intros h e He. rewrite zmask_pow2, land_ones_mod by lia. reflexivity. Qed.

Definition ffmsg_addr (a : Z) : Z :=
  if a =? MSG_invalid_literal_length_code then 0x2dc30
  else if a =? MSG_invalid_distance_code then 0x2dc50 else 0x2dc68.

Section Walk.

Local Ltac brc :=
  rewrite ?szwrap64_32_small by lia; rewrite ?szwrap64_small by lia; rewrite ?szwrap32_small by lia;
  rewrite ?mod64_id by lia; rewrite ?mod32_id by lia; lia.

Local Ltac mlia := Z.to_euclidean_division_equations; lia.

Local Ltac nf :=
  cbn [f_in f_out f_hold f_bits f_len f_dist f_op f_from f_ob fset_in fset_out fset_hold fset_bits fset_len fset_dist fset_op fset_from fset_ob x_window x_input x_wsize x_wnext x_whave ffx_of];
  rewrite ?cpn_in, ?cpn_out, ?cpn_hold, ?cpn_bits, ?cpn_len, ?cpn_dist, ?cpn_ob, ?cpn_from, ?fr_add_win, ?fr_add_out;
  cbn [f_in f_out f_hold f_bits f_len f_dist f_op f_from f_ob fset_in fset_out fset_hold fset_bits fset_len fset_dist fset_op fset_from fset_ob x_window x_input x_wsize x_wnext x_whave ffx_of].

End Walk.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
