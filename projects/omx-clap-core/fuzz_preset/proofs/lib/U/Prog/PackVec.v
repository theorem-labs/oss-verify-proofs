From Stdlib Require Import ZArith List Bool Lia Arith Permutation.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0g YO0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import AllocPack AllocPackRoom Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes PackFit PackOwn PackReparse.
Import ListNotations.
Local Open Scope Z_scope.

Definition pq_bi (k n : Z) : Z := if band n =? k then 1 else 0.

Definition pq_ev (k : Z) (e : ev) : Z :=
  match e with
  | EAlloc n => pq_bi k (Z.of_nat n + 16)
  | EGrow m n =>
      if Nat.eqb m 0 then pq_bi k (Z.of_nat n + 16)
      else if band (Z.of_nat n + 16) <? band (Z.of_nat m + 16) then pq_bi k (Z.of_nat n + 16)
      else pq_bi k (Z.of_nat n + 16) - pq_bi k (Z.of_nat m + 16)
  | EFail _ => 0
  | EFree n => - pq_bi k (Z.of_nat n + 16)
  end.

Fixpoint pq_run (k : Z) (tr : list ev) : Z :=
  match tr with
  | [] => 0
  | e :: r => pq_ev k e + pq_run k r
  end.

Fixpoint pq_frees (k : Z) (D : list (Z * Z)) : Z :=
  match D with
  | [] => 0
  | ak :: r => - pq_bi k (snd ak + 16) + pq_frees k r
  end.

Definition pq_BMAX : Z := 2 ^ 44.

Definition pq_NMAX : Z := 2 ^ 29 - 8192.

Definition tr_prof (tr : list ev) (V : Z -> Z) (s hb : Z) : Prop :=
  (forall p r, tr = p ++ r ->
     (forall k, 0 <= k < 49 -> pq_run k p <= V k + s) /\ held p + 16 * nlive p <= hb) /\
  (forall e, In e tr -> is_call e = true -> Z.of_nat (esize e) + 16 <= 2 ^ 28).

Definition tr_fin (tr : list ev) (V : Z -> Z) : Prop :=
  forall k, 0 <= k < 49 -> pq_run k tr <= V k.

Fixpoint pq_cb (t : jv) : list nat :=
  match t with
  | JArr items => rkb false (rfcap (length items) 0 0) ++ flat_map pq_cb items
  | JObj ms => rkb true (rfcap (length ms) 0 0) ++ flat_map (fun '(_, u) => pq_cb u) ms
  | _ => []
  end.
