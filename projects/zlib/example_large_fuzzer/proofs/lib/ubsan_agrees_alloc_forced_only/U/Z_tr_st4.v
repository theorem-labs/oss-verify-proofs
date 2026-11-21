(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_tr_emit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma wrap16_eqm16 : forall V V', V' mod 2^16 = V mod 2^16 -> wrap16 V' = wrap16 V.
Proof. intros V V' H. rewrite !wrap16_mod. exact H. Qed.

Lemma nbv_eqm : forall BB k V V', V' mod 2^16 = V mod 2^16 -> nbv BB k V' = nbv BB k V.
Proof. intros BB k V V' H. unfold nbv. rewrite (wrap16_eqm16 V V' H). reflexivity. Qed.

(* [comment removed for export] *)

