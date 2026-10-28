(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase AZ_kit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma bv64_eqm_k : forall x y, x mod 2^64 = y mod 2^64 -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof. intros x y H. rewrite <- (Z_to_bv64_mod x), <- (Z_to_bv64_mod y), H. reflexivity. Qed.

(* [comment removed for export] *)
Ltac kit_sh_fix :=
  repeat match goal with
  | |- context [Z_to_bv 64 (-1 * ?t + -18446744073709551552)] =>
      replace (Z_to_bv 64 (-1 * t + -18446744073709551552)) with (Z_to_bv 64 (64 - t))
        by (apply bv64_eqm_k; replace (-1 * t + -18446744073709551552) with ((64 - t) + (-1) * 2^64) by lia;
            rewrite Z.mod_add by lia; reflexivity)
  end.

Tactic Notation "kx_autoFA_v" constr(VMAX) uconstr(AKS) uconstr(STOPS) constr(FUEL) uconstr(KZS) uconstr(RRS) uconstr(WWS) :=
  let stops := constr:(STOPS : list Z) in let aks := constr:(AKS : list kza) in let kzs := constr:(KZS : list kz) in
  let rrs := constr:(RRS : list (Z * Z)) in let wws := constr:(WWS : list (Z * Z)) in
  kx_autoFA_core (VMAX : Z) stops (FUEL : nat) true aks kzs rrs wws.

(* [comment removed for export] *)
Lemma unp_carry2 : forall (m0 mm : amem) A an B bn lo0 hi0,
  unpoisoned m0 lo0 hi0 -> munch [(A, A + an); (B, B + bn)] m0 mm ->
  4096 <= lo0 -> hi0 <= 2^47 ->
  (an <= 0 \/ (A + an <= 0x7fff8000 \/ 0x10007fff8000 <= A)) ->
  (bn <= 0 \/ (B + bn <= 0x7fff8000 \/ 0x10007fff8000 <= B)) ->
  unpoisoned mm lo0 hi0.
Proof.
  intros m0 mm A an B bn lo0 hi0 U MU L0 H0 HA HB.
  eapply unpoisoned_agree; [exact U|]. intros s Hs. apply MU.
  rewrite !shad_div in Hs. unfold ASHOFF in Hs.
  rewrite wa_unsigned by (Z.div_mod_to_equations; lia).
  cbn [outside]. repeat split; try exact I; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma unp_carryS : forall (m0 mm : amem) A an SPV fr lo0 hi0,
  unpoisoned m0 lo0 hi0 -> munch [(A, A + an); (SPV - fr, SPV)] m0 mm ->
  4096 <= lo0 -> hi0 <= 2^47 ->
  (an <= 0 \/ (A + an <= 0x7fff8000 \/ 0x10007fff8000 <= A)) -> 0x10007fff8000 <= SPV - fr ->
  unpoisoned mm lo0 hi0.
Proof.
  intros m0 mm A an SPV fr lo0 hi0 U MU L0 H0 HA HS.
  replace SPV with (SPV - fr + fr) in MU at 2 by lia.
  eapply (unp_carry2 m0 mm A an (SPV - fr) fr lo0 hi0 U MU L0 H0 HA). right. right. exact HS.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac kx_clear_or := repeat match goal with H : _ \/ _ |- _ => clear H | H : _ -> _ |- _ => clear H end.
Ltac kx_lia_fast :=
  first [ solve [kx_clear_or; lia]
        | solve [kx_bv_ranges; kx_clear_or; lia]
        | kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ] ].

Lemma rng_shspanZ : forall RNG A n, rng RNG (shad A) (shspan A n) -> rng RNG (KXSHLO + A / 8) (shspanZ A n).
Proof. intros RNG A n H. rewrite shad_div in H. unfold ASHOFF in H. unfold KXSHLO, shspanZ. unfold shspan in H. exact H. Qed.

(* [comment removed for export] *)
