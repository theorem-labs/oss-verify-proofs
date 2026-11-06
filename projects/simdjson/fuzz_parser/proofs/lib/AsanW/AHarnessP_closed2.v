(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Import ADkModel.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg ABase AMalloc_iface AFake_iface AU_iface AU_parts_iface AU_wild_iface
     AHarnessU_iface AH_opnew AH_opnew_nt AH_opdelW AInstanceW AInstanceW2 AClientRtW AHarnessP_closed.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import APS2_iface PA2_a2run PA2_main.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SFPA_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA2 Require Import A2_sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section Closure2.
  (* [comment removed for export] *)
  Hypothesis SFP : SUMW_T AI_W afake_rng SFPAS.
  Hypothesis PFF : SUMW_T AI_W afake_rng PFFAS.
  Hypothesis SFPC : SUMC_T AI_W afake_rng SFPCAS.
  Hypothesis PFFC : SUMC_T AI_W afake_rng PFFCAS.

  Lemma a2sound_W : A2SOUND_T AI_W.
  Proof. exact (@a2_sound rc AI_W). Qed.

  Theorem stage2_W : stage2_stmtA AI_W afake_rng.
  Proof.
    exact (stage2_proofA AI_W fflag afake_rng (sm5_of_sm5_1 AI_W fflag afake_rng crtW_sm5_1) crtW_sf5
             (opnew_nt_proofA AI_W (opnew_proofA AI_W)) opdelete_arr_wild_proofA a2sound_W crtW_rng_fs_mono SFP PFF SFPC PFFC).
  Qed.

  Theorem fuzz_closedW_mod_num : fuzz_oneU_stmt AI_W afake_rng.
  Proof. exact (fuzz_closedW_of_stage2 stage2_W). Qed.
End Closure2.
End CANSEC1.
