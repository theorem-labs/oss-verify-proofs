(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Import ADkModel.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg ABase AMalloc_iface AFake_iface AU_iface AU_parts_iface AHarnessU_iface
     AH_opnew AH_opnew_nt AInstanceW AInstanceW2 AClientRtW APC_s12iface APC_s1bridge APC_parse APC_fuzz.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2B Require Import APS2_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section Closure.
  (* [comment removed for export] *)
  Hypothesis S2 : stage2_stmtA AI_W afake_rng.

  Theorem fuzz_closedW_of_stage2 : fuzz_oneU_stmt AI_W afake_rng.
  Proof.
    exact (afuzz_proof AI_W afake_rng fflag (opnew_nt_proofA AI_W (opnew_proofA AI_W)) (opdelete_arr_proofA AI_W) (opdelete_proofA AI_W)
             crtW_IMG_CI (parse_proofA AI_W afake_rng (s1l_proofA AI_W) S2) afake_rng_mono crtW_sm2 crtW_fake_flag crtW_fake_release).
  Qed.
End Closure.
End CANSEC1.
