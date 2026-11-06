(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1cq X1d0 X1cl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib Require Import TopLevelA ObligationsA.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require Import X1rz.
Import ListNotations.

Definition no_enomem (n : node) (mo : Model) : Prop :=
match n with
| NMmap _ _ _ flags => Z.land flags MAP_FIXED_Z = 0%Z ->
forall rsp mo' evs, nstep n mo rsp mo' evs -> errno_of (eff_ret rsp) = None
| NMprotect _ _ _ => forall rsp mo' evs, nstep n mo rsp mo' evs -> errno_of (eff_ret rsp) = None
| _ => True
end.

Definition prog_no_enomem_stmt (segs : list Segment) (rstage : Z) (pc : N) (ph : PhdrInfo) (lim : Z) : Prop :=
forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
tsafe nstep no_enomem (the_prog segs rstage inp en) (mo0 segs lim en inp).
