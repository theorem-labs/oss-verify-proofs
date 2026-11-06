(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import List.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import DecOkDefs.
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
