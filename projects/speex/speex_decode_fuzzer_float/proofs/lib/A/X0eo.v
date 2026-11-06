(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cy X1cp X1cj X1dd X1cg X1cs X1cm X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X0j1 X0gi X0hr X0j3 X0hi
X0hh X0j4 X0h2 X0j6 X0gd X0gf X0fy X0fg X0d8 X0fq X0d7.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X173 X18c X19m X183 X182 X19n X17n X19p X16y X170 X16j X161 X13t X16b X13s.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X182 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X170 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13s.
Import ListNotations.
Open Scope Z_scope.

Section MalPre.
Variables (Σ : rtsA) (m : mem) (sp : word) (lo : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis CALL : call_ok RTA Σ m sp lo.
#[local] Notation L := (lay Σ).

Lemma mp_cells :
rw_cells bsegs m 0xfc0f8 [C8 (Z_to_bv 64 0x195560)] /\ rw_cells bsegs m g_GOT_common_flags [C8 (Z_to_bv 64 g_common_flags)]
/\ rw_cells bsegs m i_max_user [C8 (Z_to_bv 64 (2^40))] /\ rw_cells bsegs m i_min_rz [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)]
/\ rw_cells bsegs m g_asan_inited [C1 (Z_to_bv 8 1)] /\ rw_cells bsegs m g_malloc_context_size_cell [C4 (Z_to_bv 64 30)]
/\ rw_cells bsegs m g_rss_limit_exceeded [C1 (Z_to_bv 8 0)] /\ rw_cells bsegs m 0x195560 [C8 (Z_to_bv 64 4096)]
/\ rw_cells bsegs m (g_common_flags + 34) [C1 (Z_to_bv 8 1)]
/\ thread_cells (l_TCX L) (l_T L) m /\ stack_cells (l_T L) (l_top L) (l_top L - 0x800000) m
/\ rw_cells bsegs m (l_T L + 3168) [C1 (Z_to_bv 8 0)].
Proof.
pose proof (ART_consts Σ m HA) as (_ & (G1 & G2 & G3 & G4 & G5) & TC & _ & _ & SC & _ & ICR).
destruct ICR as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & X18 & X19 & X20 & X21 & X22 & _).
pose proof (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & (dtvbeg & _ & (T1 & _)) & _).
split; [exact G1|]. split; [exact G2|]. split; [exact X19|]. split; [exact X20|]. split; [exact T1|]. split; [exact X8|].
split; [exact X21|]. split; [exact G3|]. split; [exact X22|]. split; [exact TC|]. split; [exact SC|]. exact X1.
Qed.

Lemma mp_layout : 0 < l_TCX L /\ l_TCX L + 0xa0 <= lo /\ l_T L + 4096 <= lo /\ (l_TCX L + 0xa0 <= l_T L \/ l_T L + 4096 <= l_TCX L)
/\ kHighShadowEnd + 8 <= lo /\ 0 <= l_top L - 0x800000 < l_top L /\ 4096 <= l_top L <= 2 ^ 63
/\ (l_T L + 4096 <= 0x10000 \/ 0x65b000 <= l_T L).
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
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Section MalPre.
Variables (Σ : rtsA) (m : mem) (sp : word) (lo : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis CALL : call_ok RTA Σ m sp lo.
#[local] Notation L := (lay Σ).

Lemma mp_cells :
rw_cells asegs m 0xf3878 [C8 (Z_to_bv 64 0x18cd20)] /\ rw_cells asegs m g_GOT_common_flags [C8 (Z_to_bv 64 g_common_flags)]
/\ rw_cells asegs m i_max_user [C8 (Z_to_bv 64 (2^40))] /\ rw_cells asegs m i_min_rz [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)]
/\ rw_cells asegs m g_asan_inited [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m g_malloc_context_size_cell [C4 (Z_to_bv 64 30)]
/\ rw_cells asegs m g_rss_limit_exceeded [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m 0x18cd20 [C8 (Z_to_bv 64 4096)]
/\ rw_cells asegs m (g_common_flags + 34) [C1 (Z_to_bv 8 1)]
/\ thread_cells (l_TCX L) (l_T L) m /\ stack_cells (l_T L) (l_top L) (l_top L - 0x800000) m
/\ rw_cells asegs m (l_T L + 3168) [C1 (Z_to_bv 8 0)].
Proof.
pose proof (ART_consts Σ m HA) as (_ & (G1 & G2 & G3 & G4 & G5) & TC & _ & _ & SC & _ & ICR).
destruct ICR as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & X18 & X19 & X20 & X21 & X22 & _).
pose proof (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & (dtvbeg & _ & (T1 & _)) & _).
split; [exact G1|]. split; [exact G2|]. split; [exact X19|]. split; [exact X20|]. split; [exact T1|]. split; [exact X8|].
split; [exact X21|]. split; [exact G3|]. split; [exact X22|]. split; [exact TC|]. split; [exact SC|]. exact X1.
Qed.

Lemma mp_layout : 0 < l_TCX L /\ l_TCX L + 0xa0 <= lo /\ l_T L + 4096 <= lo /\ (l_TCX L + 0xa0 <= l_T L \/ l_T L + 4096 <= l_TCX L)
/\ kHighShadowEnd + 8 <= lo /\ 0 <= l_top L - 0x800000 < l_top L /\ 4096 <= l_top L <= 2 ^ 63
/\ (l_T L + 4096 <= 0x10000 \/ 0x652000 <= l_T L).
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
