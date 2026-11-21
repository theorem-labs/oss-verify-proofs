(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import TopLevel Obligations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition no_enomem (n : node) (mo : Model) : Prop :=
  match n with
  | NMmap _ _ _ flags => Z.land flags MAP_FIXED_Z = 0%Z ->
      forall rsp mo' evs, nstep n mo rsp mo' evs -> errno_of (eff_ret rsp) = None
  | NMprotect _ _ _ => forall rsp mo' evs, nstep n mo rsp mo' evs -> errno_of (eff_ret rsp) = None
  | _ => True
  end.

Definition prog_no_enomem_stmt (segs : list Segment) (rstage : Z) (pc : N) (ph : PhdrInfo) (lim : Z) : Prop :=
  forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
    tsafe nstep no_enomem (the_prog segs rstage inp en) (mo0 segs lim en inp).

