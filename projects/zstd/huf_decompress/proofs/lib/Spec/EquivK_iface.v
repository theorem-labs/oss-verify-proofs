(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState ITree Nodes Decode Image InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad Sim STree Malloc Stdio PState Prog StepB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require Import TopLevel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition LBND : Z := 2^31 - 2^26.   (* [comment removed for export] *)
Definition stepB := nstepB LBND.

(* [comment removed for export] *)
Definition never_forced_p_stmt : Prop := forall rs en inp,       (* [comment removed for export] *)
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
  tnf (Prog.prog psegs rs inp en) (mo0 psegs source_alloc_limit en inp).
Definition never_forced_u_stmt : Prop := forall rs en inp,
  valid_entry (mkImage usegs u_init_pc u_phdrs) en inp -> valid_input_either inp ->
  tnf (Prog.prog usegs rs inp en) (mo0 usegs target_alloc_limit en inp).

(* [comment removed for export] *)
Definition debt0 (s : PState) : list event := [].

(* [comment removed for export] *)
Definition fr_frame (FR : PState -> PState -> Prop) : Prop :=
  forall sG sC sG' sC', FR sG sC ->
    ps_fa sG' = ps_fa sG -> ps_so sG' = ps_so sG -> ps_fa sC' = ps_fa sC -> ps_so sC' = ps_so sC -> FR sG' sC'.

(* [comment removed for export] *)
Definition pin (R : rel PState PState) (sG0 sC0 : PState) : rel PState PState :=
  fun sG moG sC moC => sG = sG0 /\ sC = sC0 /\ R sG moG sC moC.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
