(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require Import TopLevel Obligations.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)
Definition no_enomem (n : node) (mo : Model) : Prop :=
  match n with
  | NMmap _ _ _ flags => Z.land flags MAP_FIXED_Z = 0%Z ->
      forall rsp mo' evs, nstep n mo rsp mo' evs -> errno_of (eff_ret rsp) = None
  | NMprotect _ _ _ => forall rsp mo' evs, nstep n mo rsp mo' evs -> errno_of (eff_ret rsp) = None
  | _ => True
  end.

(* [comment removed for export] *)
Definition prog_no_enomem_stmt (segs : list Segment) (rstage : Z) (pc : N) (ph : PhdrInfo) (lim : Z) : Prop :=
  forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
    tsafe nstep no_enomem (the_prog segs rstage inp en) (mo0 segs lim en inp).

(* [comment removed for export] *)
