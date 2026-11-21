(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BvAux.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sep (a n b m : Z) : Prop := a + n <= b \/ b + m <= a.

(* [comment removed for export] *)
Ltac sep_solve :=
  first [ lia
        | match goal with
          | H : sep _ _ _ _ |- _ =>
              let H' := fresh "Hsep" in pose proof H as H'; unfold sep in H';
              destruct H'; solve [ lia | left; lia | right; lia ]
          end ].

(* [comment removed for export] *)
Lemma szwrap32_small : forall a, -2147483648 <= a < 2147483648 -> szwrap 32 a = a.
Proof. intros a H. apply szwrap_small; [lia|]. change (2 ^ (32 - 1)) with 2147483648. lia. Qed.

Lemma szwrap64_small : forall a, -9223372036854775808 <= a < 9223372036854775808 -> szwrap 64 a = a.
Proof. intros a H. apply szwrap_small; [lia|]. change (2 ^ (64 - 1)) with 9223372036854775808. lia. Qed.

Lemma szwrap64_32_small : forall a, -2147483648 <= a < 2147483648 -> szwrap 64 (szwrap 32 a) = a.
Proof. intros a H. rewrite szwrap32_small by lia. apply szwrap64_small. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.

(* [comment removed for export] *)
Fixpoint fslots_miss (l : list (Z * nat * Z)) (o' n' : Z) : bool :=
  match l with
  | [] => true
  | (o, w, _) :: l' => ((o + Z.of_nat w <=? o') || (o' + n' <=? o)) && fslots_miss l' o' n'
  end.

End WithSegs.
