(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Monad MSafe.
Import ListNotations.
Import ITree.Exc.
Open Scope mspec_scope.
Section Sim.
Context {StG StC : Type}.
Variable debtG : StG -> list event.
Variable debtC : StC -> list event.
Variable stepG : node -> Model -> resp -> Model -> list event -> Prop.
Definition rel : Type := StG -> Model -> StC -> Model -> Prop.
Definition fsim {A B} (R : rel) (mG : M StG A) (mC : M StC B) (Q : A -> B -> rel) : Prop :=
forall sG moG sC moC, R sG moG sC moC ->
(forall trG a sG' moG', tpath stepG (mG sG) moG trG (Ok (a, sG')) moG' ->
exists trC b sC' moC' v,
tpath nstep (mC sC) moC trC (Ok (b, sC')) moC'
/\ trG ++ debtG sG' = debtG sG ++ v /\ trC ++ debtC sC' = debtC sC ++ v
/\ Q a b sG' moG' sC' moC')
/\ (forall trG, texit stepG nexit (mG sG) moG trG ->
exists trC v, texit nstep nexit (mC sC) moC trC /\ trG = debtG sG ++ v /\ trC = debtC sC ++ v).
End Sim.
Arguments rel StG StC : clear implicits.
