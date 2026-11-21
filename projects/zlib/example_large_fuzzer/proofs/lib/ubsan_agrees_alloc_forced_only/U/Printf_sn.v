(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Prelim Monad PrintfModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Printf_lib F_printf_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zlength_app : forall {A} (a b : list A), zlength (a ++ b) = zlength a + zlength b.
Proof. intros. unfold zlength. rewrite length_app. lia. Qed.

Lemma mbind_eq : forall {St A B} (m : M St A) (f : A -> M St B) s a s',
  m s = ITree.Ret (Ok (a, s')) -> mbind m f s = f a s'.
Proof. intros St A B m f s a s' H. unfold mbind, ebind. rewrite H. reflexivity. Qed.

Lemma mbind_mbind_eq : forall {St A B C} (m : M St A) (f : A -> M St B) (g : B -> M St C) s a s',
  m s = ITree.Ret (Ok (a, s')) -> mbind (mbind m f) g s = mbind (f a) g s'.
Proof. intros St A B C m f g s a s' H. unfold mbind, ebind. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Ltac msn E := first [ rewrite (mbind_mbind_eq _ _ _ _ _ _ E) | rewrite (mbind_eq _ _ _ _ _ E) ]; cbv beta.

