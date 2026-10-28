(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_tlsgetaddr R_fs_defs R_unwind_defs R_asan_defs R_asan_malloc RT_state RT_rep RT_facts0 RT_sep RT_facts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GW}.
Section MalPre.
Variables (Σ : rtsA) (m : mem) (sp : word) (lo : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis CALL : call_ok RTA Σ m sp lo.
#[local] Notation L := (lay Σ).

Lemma mp_cells :
  rw_cells bsegs m 0x16e750 [C8 (Z_to_bv 64 0x207660)] /\ rw_cells bsegs m g_GOT_common_flags [C8 (Z_to_bv 64 g_common_flags)]
  /\ rw_cells bsegs m i_max_user [C8 (Z_to_bv 64 (2^40))] /\ rw_cells bsegs m i_min_rz [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)]
  /\ rw_cells bsegs m g_asan_inited [C1 (Z_to_bv 8 1)] /\ rw_cells bsegs m g_malloc_context_size_cell [C4 (Z_to_bv 64 30)]
  /\ rw_cells bsegs m g_rss_limit_exceeded [C1 (Z_to_bv 8 0)] /\ rw_cells bsegs m 0x207660 [C8 (Z_to_bv 64 4096)]
  /\ rw_cells bsegs m (g_common_flags + 34) [C1 (Z_to_bv 8 1)]
  /\ thread_cells (l_TCX L) (l_T L) m /\ stack_cells (l_T L) (l_top L) (l_top L - 0x800000) m
  /\ rw_cells bsegs m (l_T L + 3168) [C1 (Z_to_bv 8 0)].
Proof.
  pose proof (ART_consts Σ m HA) as (_ & (G1 & G2 & G3 & G4 & G5) & TC & _ & _ & SC & _ & ICR).
  destruct ICR as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & X18 & X19 & X20 & X21 & X22 & _).
  pose proof (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & (dtvbeg & _ & (T1 & _)) & _).
  split; [exact G1|]. split; [exact G2|]. split; [exact X19|]. split; [exact X20|]. split; [exact T1|]. split; [exact X8|].
  split; [exact X21|]. split; [exact G3|]. split; [exact X22|]. split; [exact TC|]. split; [exact SC|]. exact X1.
Qed.

Lemma mp_layout : 0 < l_TCX L /\ l_TCX L + 0xa0 <= lo /\ l_T L + 4096 <= lo /\ (l_TCX L + 0xa0 <= l_T L \/ l_T L + 4096 <= l_TCX L)
  /\ kHighShadowEnd + 8 <= lo /\ 0 <= l_top L - 0x800000 < l_top L /\ 4096 <= l_top L <= 2 ^ 63
  /\ (l_T L + 4096 <= 0x10000 \/ 0x6ce000 <= l_T L).
Proof.
  destruct CALL as (_ & LOW & _ & _ & _). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0 in LOW.
  pose proof (geo_layout Σ m HA) as HL. unfold layout_ok in HL.
  destruct HL as ((W1 & W2) & X3 & (T1 & T2) & T3 & _ & _ & _ & _ & (G1 & G2 & G3 & G4 & G5) & (H1 & H2 & H3 & H4 & H5) & _ & _ & _ & _ & _
                  & _ & _ & _ & _ & _ & Ha & _).
  unfold l_ACEIL, STACK_WIN, sp_window_lo, sp_window_hi, kHighShadowEnd, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SEGTOP_A in *.
  unfold apart in Ha. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  destruct G5 as [G5|G5]; [left | right]; lia.
Qed.

End MalPre.

End GWIN.
