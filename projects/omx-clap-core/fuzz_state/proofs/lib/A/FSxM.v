(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* fuzz_state's malloc / free runtime fields in FsRt form: each theorem is the type of a FsRt field of lib/A/FSH_Rt.v
   (fr_malloc, fr_free) at segs := tfibsegs, so that the two fields are discharged by a proved theorem.  The address
   conjunct holds because TfibSyms fixes as_code B to Tfib_code (AF0m.ts_code), whose pc_wrap_malloc / pc_wrap_free
   (AF0l.v:11-12) are FSH_Base's PC_malloc / PC_free (the symbols __wrap_malloc 0x53074 / __wrap_free 0x53070).  The
   realizes conjunct is the proved allocator top: FSupoisonAllocM.tfib_amalloc_realizesU and
   FSupoisonAllocF.afree_realizes_allU.  This file proves no function of its own.  No Axiom, no Admitted.
   rule 24: no function proved. *)
(* Modified by Theorem Labs, 2026-10: new file; FsRt-field forms of fuzz_state's malloc / free tops. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YM05 YG0f YG0d YF0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AF0l AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSH_Base FSupoisonU FSupoisonAllocM FSupoisonAllocF.
Import ListNotations.
Local Open Scope Z_scope.

Section x. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The type of FsRt.fr_malloc (lib/A/FSH_Rt.v:124) at segs := tfibsegs. *)
Theorem fr_malloc_U : forall B, TfibSyms B -> (forall t, as_dhash B t = tfib_dhash t) ->
pc_wrap_malloc (as_code B) = FSH_Base.PC_malloc /\ FSupoisonU.amalloc_realizesU tfibsegs B.
Proof.
intros B TS HD. split.
- rewrite (ts_code B TS). reflexivity.
- exact (FSupoisonAllocM.tfib_amalloc_realizesU B TS HD).
Qed.

(* The type of FsRt.fr_free (lib/A/FSH_Rt.v:125) at segs := tfibsegs. *)
Theorem fr_free_U : forall B, AR_laws tfibsegs B -> TfibSyms B -> (forall t, as_dhash B t = tfib_dhash t) ->
pc_wrap_free (as_code B) = FSH_Base.PC_free /\ FSupoisonU.afree_realizesU tfibsegs B.
Proof.
intros B LAWS TS HD. split.
- rewrite (ts_code B TS). reflexivity.
- exact (FSupoisonAllocF.afree_realizes_allU B LAWS TS HD).
Qed.

End x.
