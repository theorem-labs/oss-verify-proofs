(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prelim Monad STree Malloc Stdio HexModel Target Driver Prog LibProg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Class LibModel : Type := mkLibModel {
  LS : Type;
  lib_init : lprog LS;
  lib_one : LS -> list Z -> lprog (LS * Z)
}.

Section WithCeiling. Context {CE__ : Ceiling}.
Context {LM : LibModel}.

Local Notation MP := (Monad.M PState) (only parsing).

(* [comment removed for export] *)
Definition lib_init_prog : MP LS := interp lib_init.
Definition lib_one_prog (ls : LS) (d : list Z) : MP (LS * Z) := interp (lib_one ls d).

Definition lib_free_optG (p : option bptr) : MP unit :=
  match p with Some q => raw_free q | None => mret tt end.

(* [comment removed for export] *)
Fixpoint run_callsG (d : list Z) (n : nat) (ls : LS) (rc : Z) : MP Z :=
  match n with
  | O => mret rc
  | S n' =>
      p <- lib_one_prog ls d ;;
      stdout_vprintf ps_so set_so_ps (pieces_emit_of (Zdecimal (snd p) ++ [10])) ;;;      (* [comment removed for export] *)
      run_callsG d n' (fst p) (snd p)
  end.

(* [comment removed for export] *)
Definition target_runG (cfg : Z) (payload : list Z) : MP Z :=
  ls0 <- lib_init_prog ;;                                     (* [comment removed for export] *)
  let calls := Z.to_nat (Z.land cfg 3 + 1) in
  let plen := zlength payload in
  a <- (if plen =? 0 then mret (Some None)                    (* [comment removed for export] *)
        else r <- raw_malloc plen ;;
             mret (match r with None => None | Some p => Some (Some p) end)) ;;
  match a with
  | None => mret 2                                            (* [comment removed for export] *)
  | Some owned =>
      rc <- run_callsG payload calls ls0 0 ;;
      lib_free_optG owned ;;;                                 (* [comment removed for export] *)
      mret (if rc =? 0 then 0 else 1)
  end.

Definition runG (cfg : Z) (payload : list Z) : MP Z := target_runG cfg payload.

Definition prog_withG (rstage : Z) (argv : list (list Z)) : MP Empty_set :=
  startup ;;;
  code <- main_model io raw_malloc raw_free rstage alloc_init runG alloc_count argv ;;
  exit_model io exit_hook code.

(* [comment removed for export] *)
Definition progG (segs : list Segment) (rstage : Z) (argv : list (list byte)) : itree node (exc unit) :=
  ebind (prog_withG rstage (argv_Z argv) (ps_init (reservedZ segs)))
        (fun p => match fst p : Empty_set with end).

End WithCeiling.
