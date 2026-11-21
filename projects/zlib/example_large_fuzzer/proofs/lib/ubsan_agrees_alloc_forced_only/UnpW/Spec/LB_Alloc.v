(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Export LB_Logic LB_Inv LB_StmtA LB_Raw LB_Init.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import Prog LB_WMalloc.
Open Scope Z_scope.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section WithCeiling. Context {CE__ : Ceiling}.

Definition raw_malloc_LQ := raw_malloc_L malloc_core_fq_proof.
Definition raw_free_LQ := raw_free_L.

Check (raw_malloc_LQ : forall X P n, 0 <= n ->
  mspecL LBUDGET (fun s mo => QI X P s mo /\ ROOMX X P n /\ PHI P + R63X X + bigb n <= LBUDGET) (raw_malloc n)
         (fun r s mo => match r with
                        | Some p => QI ((p, n) :: X) P s mo /\ n < 2 ^ 63
                        | None => QI X P s mo
                        end)).
Check (raw_free_LQ : forall X P p n, mspecL LBUDGET (QI ((p, n) :: X) P) (raw_free p) (fun _ => QI X P)).

End WithCeiling.
