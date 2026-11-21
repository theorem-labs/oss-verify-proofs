(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode Image InitMem CTree.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Spec Require Import Prelim Monad CMonad STree Malloc Stdio PState HarnessC Adapter AdapterC Driver DriverC Prog.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import ExFlushIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Notation MCP := (MC PState).

Definition brid (p : bptr) : N := fst (fst p).
Definition fresh_top (s0 s1 : PState) (p : bptr) : Prop :=
  (s_regions (ps_m s0)) !! (brid p) = None
  /\ (s_groups (ps_m s1)) !! (brid p, 0) <> None
  /\ map_Forall (fun (b : aptr) (_ : ghdr) => fst b = brid p -> b = (brid p, 0)) (s_groups (ps_m s1)).
#[global] Instance fresh_top_dec s0 s1 p : Decision (fresh_top s0 s1 p).
Proof. unfold fresh_top. apply _. Qed.
Definition fresh_topb (s0 s1 : PState) (p : bptr) : bool := bool_decide (fresh_top s0 s1 p).
Lemma fresh_topb_true : forall s0 s1 p, fresh_topb s0 s1 p = true <-> fresh_top s0 s1 p.
Proof. intros. unfold fresh_topb. apply bool_decide_eq_true. Qed.

Section FM.
Variable FM : flush_model.

Definition fuzz_oneM : list Z -> Monad.M PState Z := HarnessC.fuzz_one_m FM raw_malloc raw_free fresh_topb.
Definition fuzz_oneC : list Z -> MCP Z := HarnessC.fuzz_one FM raw_malloc raw_free fresh_topb.
Lemma fuzz_oneC_eq : forall d, fuzz_oneC d = clift (fuzz_oneM d).
Proof. reflexivity. Qed.
Definition runC (cfg : Z) (payload : list Z) : MCP Z :=
  AdapterC.target_run raw_malloc raw_free fuzz_oneC (io_emit io) cfg payload.

Definition prog_withC (rs : Z) (argv : list (list Z)) : MCP Empty_set :=
  cmbind (clift startup) (fun _ =>
  cmbind (DriverC.main_model io raw_malloc raw_free rs alloc_init runC alloc_count argv) (fun code =>
  DriverC.exit_model io code)).

Definition prog_withD (D : hist -> bool) (rs : Z) (argv : list (list Z)) : Monad.M PState Empty_set :=
  RES D [] (prog_withC rs argv).

Definition progD_itree (D : hist -> bool) (segs : list Segment) (rs : Z) (argv : list (list byte)) (atop : Z) : itree node (exc unit) :=
  ebind (prog_withD D rs (argv_Z argv) (ps_init (reservedZ segs) atop))
        (fun p => match fst p : Empty_set with end).

Definition progD (D : hist -> bool) (segs : list Segment) (rs : Z) (inp : ProcInput) (en : ExecEntry) : itree node (exc unit) :=
  progD_itree D segs rs (in_argv inp) (entry_atop en).

Definition progC_tree (segs : list Segment) (rs : Z) (inp : ProcInput) (en : ExecEntry) : ctree node (exc unit) :=
  cebind (prog_withC rs (argv_Z (in_argv inp)) (ps_init (reservedZ segs) (entry_atop en)))
         (fun p => match fst p : Empty_set with end).

Lemma res_after_empty : forall {S} D (c : ctree node (exc (Empty_set * S))) h
    (f : Empty_set * S -> ctree node (exc unit)) (g : Empty_set * S -> itree node (exc unit)),
  res D h (cebind c f) = ebind (res D h c) g.
Proof.
  intros S D c. induction c as [r|n k IH|a IHa b IHb]; intros h f g.
  - destruct r as [|[[] ?]]. reflexivity.
  - cbn. f_equal. apply FunctionalExtensionality.functional_extensionality. intros rsp. apply IH.
  - cbn. destruct (D h); [apply IHa| apply IHb].
Qed.

Lemma res_progC_tree : forall D segs rs inp en, res D [] (progC_tree segs rs inp en) = progD D segs rs inp en.
Proof. intros. unfold progC_tree, progD, progD_itree, prog_withD, RES. apply res_after_empty. Qed.
End FM.
