(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Prelim Monad Stdio ZApi ZTarget ZApiL. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import ZInstL. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import ZTargetL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Definition pieces_emit_of (bs : list Z) : list (list Z) :=
  match bs with
  | [48; 10] => pieces_emit_0
  | _ => [bs]            (* [comment removed for export] *)
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

Definition target_run (cfg : Z) (payload : list Z) : M St Z :=
  ZTargetL.target_runL ops the_zapiL payload [cfg].

End Target.
