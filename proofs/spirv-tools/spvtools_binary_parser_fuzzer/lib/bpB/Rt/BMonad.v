(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BLPropExec BMState BMem BExec BITree BLNodes.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Import BITree.Exc.

Section Monad.
Context {St : Type}.

Definition M (A : Type) : Type := St -> itree node (exc (A * St)).

Definition mret {A} (a : A) : M A := fun s => Ret (Ok (a, s)).
Definition mbind {A B} (m : M A) (f : A -> M B) : M B :=
  fun s => ebind (m s) (fun p => f (fst p) (snd p)).
Definition munr {A} : M A := fun _ => Ret Unr.
Definition mget : M St := fun s => Ret (Ok (s, s)).
Definition mput (s : St) : M unit := fun _ => Ret (Ok (tt, s)).
Definition mupd (f : St -> St) : M unit := fun s => Ret (Ok (tt, f s)).
Definition msys {A} (n : node) (dec : resp -> option A) : M A :=
  fun s => enode n (fun r => match dec r with Some a => Some (a, s) | None => None end).
Definition mwhen (b : bool) (m : M unit) : M unit := if b then m else mret tt.
Definition massert (b : bool) : M unit := if b then mret tt else munr.

Fixpoint mloop {X R} (fuel : nat) (body : X -> M (X + R)) (x : X) : M R :=
  match fuel with
  | O => munr
  | S fuel' => mbind (body x) (fun s => match s with
                                        | inl x' => mloop fuel' body x'
                                        | inr r => mret r
                                        end)
  end.

Section Machine.
Variable segs : list Segment.

Definition implM {A} (c : M A) (s : St) (Q : A -> St -> machine_state -> Prop) (ms : machine_state) : Prop :=
  impl segs (at_node segs) (c s) (epost (fun p => Q (fst p) (snd p))) ms.

End Machine.
End Monad.

Arguments M St A : clear implicits.

Declare Scope mspec_scope.
Notation "x <- m ;; k" := (mbind m (fun x => k)) (at level 100, m at next level, right associativity) : mspec_scope.
Notation "m ;;; k" := (mbind m (fun _ => k)) (at level 100, right associativity) : mspec_scope.
Notation "' p <- m ;; k" := (mbind m (fun x => let 'p := x in k)) (at level 100, p pattern, m at next level, right associativity) : mspec_scope.
