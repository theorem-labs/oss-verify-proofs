(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import PropExec MState Frame Exec ITree Nodes RegsEquiv Image.
From OSSVerify.Proofs.openssl.punycode.lib Require Import TopLevel.
From OSSVerify.Proofs.openssl.punycode.lib.Spec Require Import Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition run_ceiling (en : ExecEntry) : Ceiling := ceiling_of_sp (bv_unsigned (en_sp en)).
Definition the_prog (segs : list Segment) (rstage : Z) : prog_tree (Exc.exc unit) :=
  fun inp en => @prog (run_ceiling en) segs rstage (in_argv inp).
Definition the_post : unit -> machine_state -> Prop := fun _ _ => True.
