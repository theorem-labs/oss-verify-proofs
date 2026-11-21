(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ISLayout.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BvAux.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateInit1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateA_NAME.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateA_EXTRA.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateA_FLAGS.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateA_COPY.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateA_DISTEXT.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateA_DIST2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateA_MATCH1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateA_MATCH2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition msv (s : inflate_state) (c : icall) (r : iregs) (from : fromptr) : Z -> Z :=
  mc_src (is_window s) (ic_outbuf c) (ir_put r) from.
Definition mdd (r : iregs) (from : fromptr) (n : Z) : Z :=
  match from with FWin _ => n + 8 | FOut i => ir_put r - i end.

Definition mt_r (r : iregs) (n : Z) : iregs := irset_put (irset_left r (wrap32 (ir_left r - n))) (ir_put r + n).
Definition mt_c (s : inflate_state) (c : icall) (r : iregs) (from : fromptr) (n : Z) : icall :=
  icset_outbuf c (mc_obn (is_window s) (ic_outbuf c) (ir_put r) from (Z.to_nat n)).

Local Ltac sxu :=
  match goal with
  | |- szwrap 32 ?a mod 2 ^ 64 < szwrap 32 ?b mod 2 ^ 64 => apply (proj2 (sxu_lt a b ltac:(lia) ltac:(lia))); lia
  | |- szwrap 32 ?a mod 2 ^ 64 <= szwrap 32 ?b mod 2 ^ 64 => apply (proj2 (sxu_le a b ltac:(lia) ltac:(lia))); lia
  | |- ~ (szwrap 32 ?a mod 2 ^ 64 < szwrap 32 ?b mod 2 ^ 64) => intros X; apply (proj1 (sxu_lt a b ltac:(lia) ltac:(lia))) in X; lia
  | |- ~ (szwrap 32 ?a mod 2 ^ 64 <= szwrap 32 ?b mod 2 ^ 64) => intros X; apply (proj1 (sxu_le a b ltac:(lia) ltac:(lia))) in X; lia
  | |- szwrap 32 ?a mod 2 ^ 64 <> szwrap 32 ?b mod 2 ^ 64 => intros X; apply (proj1 (sxu_eq a b ltac:(lia) ltac:(lia))) in X; lia
  | |- szwrap 32 ?a mod 2 ^ 64 = szwrap 32 ?b mod 2 ^ 64 => apply (proj2 (sxu_eq a b ltac:(lia) ltac:(lia))); lia
  | |- szwrap 32 ?a mod 2 ^ 64 <> 0 => intros X; apply (proj1 (szwrap32_mod64_zero a ltac:(lia))) in X; lia
  | |- szwrap 32 ?a mod 2 ^ 64 = 0 => apply (proj2 (szwrap32_mod64_zero a ltac:(lia))); lia
  end.

Section ArmMATCH.
  Variable arm_ok : Z -> iw -> bool.
  Hypothesis OK_MATCH : forall flush w, is_mode (w_s w) = MATCH -> arm_ok flush w = true ->
    leave_okb (w_s w) = true /\ match_okb (w_s w) = true.
  Definition wcopy (s : inflate_state) (copyw : Z) : Z :=
    if is_wnext s <? copyw then copyw - is_wnext s else copyw.
  Definition wfrom (s : inflate_state) (copyw : Z) : fromptr :=
    if is_wnext s <? copyw then FWin (is_wsize s - (copyw - is_wnext s)) else FWin (is_wnext s - copyw).
  Definition lmin (s : inflate_state) (x : Z) : Z := if is_length s <? x then is_length s else x.
  Local Ltac kin := cbn; repeat (first [ left; reflexivity | right ]).
End ArmMATCH.
