(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ISLayout.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BvAux.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateInit1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateArmLib3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Fixpoint lecomb (n : nat) (f : Z -> Z) : Z :=
  match n with O => 0 | S n' => f 0 + 256 * lecomb n' (fun t => f (t + 1)) end.

Lemma sxu_eq : forall x y, 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 ->
  (szwrap 32 x mod 2 ^ 64 = szwrap 32 y mod 2 ^ 64 <-> x = y).
Proof. intros x y Hx Hy. unfold szwrap. change (2 ^ (32 - 1)) with 2147483648. Z.to_euclidean_division_equations; lia. Qed.

Section CopyLoops.
  Variable P0 : Z.
Variable NO : Z.
Variable put0 : Z.
Variable n : Z.
Variable FROM : Z.
Variable dd : Z.
Variable SPV : Z.
Variable S2V : Z.
Variable sv : Z -> Z.
Variable ob : arr.
  Local Notation D := (P0 + put0).

  Definition g (p : Z) : Z := if p <? put0 then arr_get ob p else sv (p - put0).

  Hypothesis HP0 : 0 < P0 /\ P0 + NO < 2 ^ 63.
  Hypothesis Hput : 0 <= put0 /\ put0 + n <= NO.
  Hypothesis Hn : 0 < n < 2 ^ 32.
  Hypothesis HFROM : 0 <= FROM /\ FROM + n < 2 ^ 63.
  Hypothesis Hsv : forall m, 0 <= m < n -> 0 <= sv m < 256.
  Hypothesis Hob : forall p, 0 <= p < put0 -> 0 <= arr_get ob p < 256.

  Hypothesis HSPV : 0x36000 <= SPV /\ SPV + 208 < 2 ^ 63.
  Hypothesis HS2V : 0 <= S2V < 2 ^ 64.
  Hypothesis Hsep_slot : SPV + 208 <= P0 \/ P0 + NO <= SPV.
End CopyLoops.

Section CopyJob.
  Variable P0 : Z.
Variable NO : Z.
Variable put0 : Z.
Variable n : Z.
Variable FROM : Z.
Variable dd : Z.
Variable SPV : Z.
Variable S2V : Z.
Variable sv : Z -> Z.
Variable ob : arr.
  Local Notation D := (P0 + put0).
End CopyJob.
