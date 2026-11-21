(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim Monad Stdio ZApi ZTarget ZApiL ZHarnessL ZApiC ZHarnessC ZInstC ZTargetC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Definition AEF_EXIT_STATUS : Z := 77.

Definition pieces_emit_of (bs : list Z) : list (list Z) :=
  match bs with
  | [48; 10] => pieces_emit_0
  | _ => [bs]
  end.

Section Target.
Context {St ptr : Type}.
Variable raw_malloc : Z -> M St (option ptr).
Variable raw_free : ptr -> M St unit.
Context (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

Definition lib_free_opt (p : option ptr) : M St unit :=
  match p with Some q => raw_free q | None => mret tt end.

Definition ops : target_ops (M St) ptr :=
  mkOps (fun A (a : A) => mret a)
        (fun A B (m : M St A) (f : A -> M St B) => mbind m f)
        (fun A => munr)
        raw_malloc
        lib_free_opt
        (fun bs => stderr_fprintf [bs])
        (fun bs => stdout_vprintf get_so set_so (pieces_emit_of bs))
        (fun _ => mret tt)
        (fun bs => stderr_fwrite bs).

Definition err_pieces (ps : list (list Z)) : M St unit := stderr_fprintf ps.

Definition cb_exit_prog : M St Empty_set :=
  stdout_exit_flush get_so set_so ;;; msys (NExit AEF_EXIT_STATUS) dec_exit.

Definition cb_exit (A : Type) : M St A :=
  mbind cb_exit_prog (fun e => match e with end).

Definition target_run (cfg : Z) (payload : list Z) : M St Z :=
  ZTargetC.target_runC ops err_pieces cb_exit the_zapiC payload [cfg].

End Target.
