(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import List.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import DecOkDefs_u5.
Import ListNotations.
Module DK5.
Definition DKINDS : list DOK.kind :=
  [DOK.KEnt; DOK.KEnt; DOK.KEnt; DOK.KSc DOK.G0 DOK.CDig; DOK.KSc DOK.G0 DOK.CDot; DOK.KSc DOK.G1 DOK.CDig; DOK.KSc DOK.GS4 DOK.CDig; DOK.KSc DOK.GS4 DOK.CDig; 
   DOK.KSc DOK.GS4 DOK.CDig; DOK.KSc DOK.GS4 DOK.CDig; DOK.KSc DOK.GS4 DOK.CDig; DOK.KSc DOK.GS4 DOK.CDig; DOK.KSc DOK.GS4 DOK.CDig; DOK.KSc DOK.GS4 DOK.CDig; DOK.KSc DOK.GS4 DOK.CDig; DOK.KSc DOK.GS4 DOK.CDig; 
   DOK.KSc DOK.GS4 DOK.CDot; DOK.KSc DOK.GS4 DOK.CDot; DOK.KSc DOK.GS4 DOK.CDot; DOK.KSc DOK.GS4 DOK.CDot; DOK.KSc DOK.GS4 DOK.CDot; DOK.KSc DOK.GS4 DOK.CDot; DOK.KSc DOK.GS4 DOK.CDot; DOK.KSc DOK.GS4 DOK.CDot; 
   DOK.KSc DOK.GS4 DOK.CDot; DOK.KSc DOK.GS4 DOK.CStopS; DOK.KSc DOK.GS4 DOK.CStopS; DOK.KSc DOK.GS4 DOK.CStopS; DOK.KSc DOK.GS4 DOK.CStopS; DOK.KSc DOK.GS4 DOK.CStopS; DOK.KSc DOK.GS4 DOK.CStopS; DOK.KSc DOK.GS4 DOK.CStopS; 
   DOK.KSc DOK.GS4 DOK.CStopS; DOK.KSc DOK.GS4 DOK.CStopS; DOK.KSc DOK.GS4 DOK.CStopS; DOK.KSc DOK.GS4 DOK.CStopS; DOK.KSc DOK.GS4 DOK.CStopS; DOK.KSc DOK.GS4 DOK.CStopS; DOK.KSc DOK.GS4 DOK.CStopS; DOK.KSc DOK.GS4 DOK.CStopS; 
   DOK.KSc DOK.GS4 DOK.CStopS; DOK.KSc DOK.GS4 DOK.CStopS; DOK.KSc DOK.GS4 DOK.CStopS; DOK.KSc DOK.GS4 DOK.CStopS; DOK.KSc DOK.GS4 DOK.CStopS; DOK.KSc DOK.GS4 DOK.CStop2; DOK.KSc DOK.GS4 DOK.CStop2; DOK.KSc DOK.GS4 DOK.CStop2; 
   DOK.KSc DOK.GS4 DOK.CStop2; DOK.KSc DOK.GS4 DOK.CStop2; DOK.KSc DOK.GS4 DOK.CStop2; DOK.KSc DOK.GS4 DOK.CStop2; DOK.KSc DOK.GS4 DOK.CStop2; DOK.KSc DOK.GS4 DOK.CStop2; DOK.KSc DOK.GS4 DOK.CStop2; DOK.KSc DOK.GS4 DOK.CStopN; 
   DOK.KSc DOK.GS4 DOK.CStopN; DOK.KSc DOK.GS4 DOK.CStopN; DOK.KSc DOK.GS4 DOK.CStopN; DOK.KSc DOK.GS4 DOK.CStopN; DOK.KSc DOK.GS4 DOK.CStopN; DOK.KSc DOK.GS4 DOK.CStopN; DOK.KSc DOK.GS4 DOK.CStopN; DOK.KSc DOK.GS4 DOK.CStopN; 
   DOK.KSc DOK.GS4 DOK.CStopN; DOK.KSc DOK.GS4 DOK.CStopN; DOK.KSc DOK.GS4 DOK.CStopN; DOK.KSc DOK.GS4 DOK.CStopN; DOK.KSc DOK.GS4 DOK.CStopN; DOK.KSc DOK.GS4 DOK.CStopN; DOK.KSc DOK.GS4 DOK.CStopN; DOK.KSc DOK.GS4 DOK.CStopN; 
   DOK.KSc DOK.GS4 DOK.CStopN; DOK.KSc DOK.GS4 DOK.CStopN; DOK.KSc DOK.GS4 DOK.CStopN; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; 
   DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; 
   DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; 
   DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; 
   DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; 
   DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; 
   DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; 
   DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; 
   DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; 
   DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; 
   DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; 
   DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; 
   DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; 
   DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; 
   DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; 
   DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; 
   DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; 
   DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost; DOK.KPost].
End DK5.
