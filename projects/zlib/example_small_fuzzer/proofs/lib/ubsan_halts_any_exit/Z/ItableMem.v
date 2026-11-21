(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZSeqExecP.BvAux.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition sep (a n b m : Z) : Prop := a + n <= b \/ b + m <= a.

Lemma sep_sym : forall a n b m, sep a n b m -> sep b m a n.
Proof. intros a n b m [H|H]; [right|left]; exact H. Qed.

Lemma sep_sub : forall a n b m a' n' b' m',
  sep a n b m -> a <= a' -> a' + n' <= a + n -> b <= b' -> b' + m' <= b + m -> sep a' n' b' m'.
Proof. intros a n b m a' n' b' m' [H|H] H1 H2 H3 H4; [left|right]; lia. Qed.

Ltac sep_solve :=
  first [ lia
        | match goal with
          | H : sep _ _ _ _ |- _ =>
              let H' := fresh "Hsep" in pose proof H as H'; unfold sep in H';
              destruct H'; solve [ lia | left; lia | right; lia ]
          end ].

Lemma szwrap32_small : forall a, -2147483648 <= a < 2147483648 -> szwrap 32 a = a.
Proof. intros a H. apply szwrap_small; [lia|]. change (2 ^ (32 - 1)) with 2147483648. lia. Qed.

Lemma szwrap64_small : forall a, -9223372036854775808 <= a < 9223372036854775808 -> szwrap 64 a = a.
Proof. intros a H. apply szwrap_small; [lia|]. change (2 ^ (64 - 1)) with 9223372036854775808. lia. Qed.

Lemma szwrap64_32_small : forall a, -2147483648 <= a < 2147483648 -> szwrap 64 (szwrap 32 a) = a.
Proof. intros a H. rewrite szwrap32_small by lia. apply szwrap64_small. lia. Qed.


Section WithSegs.

Fixpoint fslots_miss (l : list (Z * nat * Z)) (o' n' : Z) : bool :=
  match l with
  | [] => true
  | (o, w, _) :: l' => ((o + Z.of_nat w <=? o') || (o' + n' <=? o)) && fslots_miss l' o' n'
  end.

Lemma fslots_miss_sub : forall l o n o' n',
  fslots_miss l o n = true -> o <= o' -> o' + n' <= o + n -> fslots_miss l o' n' = true.
Proof.
  induction l as [|[[o1 w1] v1] l IH]; intros o n o' n' H H1 H2; [reflexivity|].
  cbn [fslots_miss] in *. apply andb_prop in H as [Ha Hb].
  rewrite (IH o n o' n' Hb H1 H2), andb_true_r.
  apply orb_prop in Ha as [E|E]; apply Z.leb_le in E; apply orb_true_intro; [left|right]; apply Z.leb_le; lia.
Qed.

End WithSegs.
