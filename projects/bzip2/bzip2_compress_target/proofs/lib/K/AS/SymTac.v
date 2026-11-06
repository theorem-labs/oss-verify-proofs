(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import
  ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim WallSim StreamSim
  DrainSim StoreOk Footprint SymExec StepTac ShapeAlg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

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

Lemma edenot_lit : forall E z, edenot E (ELit z) = Z_to_bv 64 z.
Proof. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP1.
(* [comment removed for export] *)

(* [comment removed for export] *)

Section WithFP3.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
End WithFP3.
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Section WithFP6.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP6.
(* [comment removed for export] *)

Section WithFP7.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP7.
(* [comment removed for export] *)

Section WithFP8.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP8.
(* [comment removed for export] *)

Section WithFP9.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP9.
(* [comment removed for export] *)

(* [comment removed for export] *)

Section WithFP10.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP10.
(* [comment removed for export] *)

Section WithFP11.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End WithFP11.
(* [comment removed for export] *)

(* [comment removed for export] *)

Section WithFP13.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP13.
(* [comment removed for export] *)

Section WithFP14.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP14.
(* [comment removed for export] *)

Section WithFP15.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP15.
(* [comment removed for export] *)

Section WithFP16.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP16.
(* [comment removed for export] *)

Section WithFP17.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP17.
(* [comment removed for export] *)

Section WithFP18.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP18.
(* [comment removed for export] *)

Section WithFP19.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP19.
(* [comment removed for export] *)

Section WithFP20.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP20.
(* [comment removed for export] *)

Section WithFP21.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP21.
(* [comment removed for export] *)
