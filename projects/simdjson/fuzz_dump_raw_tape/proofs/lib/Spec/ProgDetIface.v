(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib Require Import TopLevel Obligations.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition mm_noerr_resp (n : node) (mo : Model) : Prop :=
  forall r m1 es, nstep n mo r m1 es -> errno_of (eff_ret r) = None.

Definition no_enomem (n : node) (mo : Model) : Prop :=
  match n with
  | NMprotect _ _ _ => mm_noerr_resp n mo /\ unforced n mo
  | NMmap _ _ _ fl => (Z.land fl MAP_FIXED_Z = 0%Z -> mm_noerr_resp n mo) /\ unforced n mo
  | _ => True
  end.

Lemma no_enomem_unforced : forall n mo, no_enomem n mo -> unforced n mo.
Proof. intros [] mo; first [intros _; exact I | intros [_ Hu]; exact Hu]. Qed.

Definition prog_no_enomem_stmt (segs : list Segment) (rstage : Z) (pc : N) (ph : PhdrInfo) (lim : Z) : Prop :=
  forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
    tsafe nstep no_enomem (the_prog segs rstage inp en) (mo0 segs lim en inp).

