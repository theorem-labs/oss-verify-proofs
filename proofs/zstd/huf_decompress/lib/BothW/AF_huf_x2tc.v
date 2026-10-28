(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface
     ADepot_iface ARep ALayout AHeapP AFake_iface AFake_arep AFake0k_iface AFake_arep0k AF_huf_tbl_iface3 AF_huf_rsc
     AH_huf_iface AH_huf_rdt2 AF_huf_dec_iface AF_huf_x2t.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section Inst.
  Variable DI : ADepotIface.
  Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
  Hypothesis HL : ahole_laws (AH DI AQ ASEC).
  Variable CI : list (Z * Z).
  Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
  Variable AI : AMallocIface.
  Hypothesis E : AHEAP AI = AHEAP_P (AH DI AQ ASEC).
  Hypothesis EC : aci AI = CI.

  (* [comment removed for export] *)
  Theorem huf_rdt_x2_closedA : huf_rdt_stmtA2 AI afake_rng huf_dt_okA AHUF_RDT_X2.
Proof.
  eapply huf_rdt_x2_proofA.
  all: try first [eapply fake_flag_AI; eassumption | eapply fake_release_AI; eassumption
                 | eapply stack_malloc_0k_AI; [eassumption ..| unfold Z.of_nat; lia]
                 | eapply huf_rstats_closedA; [eassumption ..| unfold Z.of_nat; lia] | eassumption].
Qed.
End Inst.
End CANSEC1.
