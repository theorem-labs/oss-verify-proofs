(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Zg2 MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim Monad Stdio Zpb Z3o.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

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
        mcho.

Definition target_run (cfg : Z) (payload : list Z) : M St Z :=
  Z3o.target_run ops payload [cfg].

End Target.
