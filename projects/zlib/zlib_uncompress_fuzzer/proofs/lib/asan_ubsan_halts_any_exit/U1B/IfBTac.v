(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AShadow U2AKit UbFit2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma lxor_ltb1_ne : forall a b, 0 <= a -> 0 <= b -> a <> b -> (Z.lxor a b <? 1) = false.
Proof.
  intros a b Ha Hb NE. apply Z.ltb_ge. assert (0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia).
  assert (Z.lxor a b <> 0) by (intros E; apply Z.lxor_eq in E; contradiction). lia.
Qed.

Ltac ub_close K :=
  zify_cond K; rewrite ?fub_land7, ?fub_land3, ?fub_land1 in K; rewrite ?lnot64 in K by lia;
  first [ lia | Z.div_mod_to_equations; lia ].
Ltac pc_dec_ub :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      first [ replace (if c then a else b) with b
                by (let K := fresh "K" in destruct c eqn:K; [exfalso; ub_close K | reflexivity])
            | replace (if c then a else b) with a
                by (let K := fresh "K" in destruct c eqn:K; [reflexivity | exfalso; ub_close K]) ]
  end.
Ltac ub_flags :=
  repeat match goal with
  | |- context [Z.b2z (0 <? ?X)] => replace (0 <? X) with true by (symmetry; apply Z.ltb_lt; lia); change (Z.b2z true) with 1
  | |- context [Z.b2z (Z.lxor ?A ?B <? 1)] => rewrite (lxor_ltb1_ne A B) by lia; change (Z.b2z false) with 0
  | |- context [Z.b2z (?X <? 1)] => replace (X <? 1) with false by (symmetry; apply Z.ltb_ge; lia); change (Z.b2z false) with 0
  end.
Ltac zsb := zs; ub_flags.
Ltac zrunu STOPS := repeat (first [ at_free_pc STOPS; zsb | pc_dec_ub ]).
Ltac show_br :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      idtac "BRANCH" c "->" a "|" b
  | |- _ => idtac "no branch"
  end.
