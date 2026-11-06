(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec FxLin FxCore FxSubst FxSound FxMem FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxEnt FxRgs FxFacts FxPlan FxFrame FxWork FxWorkX.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWork OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWorkX.
From OSSVerify.Proofs.fast_float.from_chars.lib.KX Require Import KxBridge KxRun.
From OSSVerify.Proofs.fast_float.from_chars.lib.HX Require Import HxGen.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition rgl (L : sst) (k : Z) : lin := rget (s_regs L) (rkz k).
Definition bv8l (l : lin) : list bval := List.map (fun j => BV l (Z.of_nat j)) (seq 0 8).
Definition fv (n : positive) (i : nat) : positive := Pos.of_nat (Pos.to_nat n + i).

(* [comment removed for export] *)
Fixpoint find_cell (rgs : list region) (a : lin) : option (region * Z * lin) :=
  match rgs with
  | [] => None
  | R :: rs =>
      match is_const (lsub a (rg_base R)) with
      | Some o =>
          match tget (okey o) (rg_cont R) with
          | Some (BV l 0) => if (tracked_b (rg_cont R) o (bv8l l) && Z.ltb o (2 ^ 32))%bool then Some (R, o, l) else find_cell rs a
          | Some (BK 0) => if (tracked_b (rg_cont R) o (List.repeat (BK 0) 8) && Z.ltb o (2 ^ 32))%bool then Some (R, o, lconst 0)
                           else find_cell rs a
          | _ => find_cell rs a
          end
      | None => find_cell rs a
      end
  end.
Lemma find_cell_spec : forall rgs a R o l, find_cell rgs a = Some (R, o, l) ->
  In R rgs /\ is_const (lsub a (rg_base R)) = Some o /\ o < 2 ^ 32 /\
  (tracked_b (rg_cont R) o (bv8l l) = true \/ (l = lconst 0 /\ tracked_b (rg_cont R) o (List.repeat (BK 0) 8) = true)).
Proof.
  induction rgs as [|R0 rs IH]; intros a R o l H; cbn [find_cell] in H; [discriminate|].
  destruct (is_const (lsub a (rg_base R0))) as [o0|] eqn:Ho.
  - destruct (tget (okey o0) (rg_cont R0)) as [[b|l0 [|j|j]]|];
      try (destruct (IH a R o l H) as (X1 & X2 & X3 & X4); split; [right; exact X1 | split; [exact X2 | split; [exact X3 | exact X4]]]).
    + destruct b as [|p|p]; try (destruct (IH a R o l H) as (X1 & X2 & X3 & X4); split; [right; exact X1 | split; [exact X2 | split; [exact X3 | exact X4]]]).
      destruct (tracked_b (rg_cont R0) o0 (List.repeat (BK 0) 8) && Z.ltb o0 (2 ^ 32))%bool eqn:Hb.
      * injection H as <- <- <-. apply andb_prop in Hb as [Hb1 Hb2]. apply Z.ltb_lt in Hb2.
        split; [left; reflexivity | split; [exact Ho | split; [exact Hb2 | right; split; [reflexivity | exact Hb1]]]].
      * destruct (IH a R o l H) as (X1 & X2 & X3 & X4). split; [right; exact X1 | split; [exact X2 | split; [exact X3 | exact X4]]].
    + destruct (tracked_b (rg_cont R0) o0 (bv8l l0) && Z.ltb o0 (2 ^ 32))%bool eqn:Hb.
      * injection H as <- <- <-. apply andb_prop in Hb as [Hb1 Hb2]. apply Z.ltb_lt in Hb2.
        split; [left; reflexivity | split; [exact Ho | split; [exact Hb2 | left; exact Hb1]]].
      * destruct (IH a R o l H) as (X1 & X2 & X3 & X4). split; [right; exact X1 | split; [exact X2 | split; [exact X3 | exact X4]]].
  - destruct (IH a R o l H) as (X1 & X2 & X3 & X4). split; [right; exact X1 | split; [exact X2 | split; [exact X3 | exact X4]]].
Qed.

Definition nof (L : sst) : list fact := [].
Definition nox (L : sst) : list xfact := [].
