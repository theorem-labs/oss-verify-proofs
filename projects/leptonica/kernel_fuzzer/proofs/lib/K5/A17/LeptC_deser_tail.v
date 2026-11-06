(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import Layout.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import RT_iface RT_traces RT_gaps_iface Lept_iface LeptC_deser2_defs Lept_deser_defs LeptC_deser0_defs LeptC_deserm1_defs LeptC_deser2 LeptM_deser1_c0 LeptM_deser1_c16 LeptC_deser0 LeptC_deserm1.
Import ListNotations.
Open Scope Z_scope.

Section TAIL.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis LSE : lept_stderr_cps RT.
Hypothesis RERR : returnError_cps RT e_returnErrorPtr.
Hypothesis HDR : pixCreateHeader_cps RT.
Hypothesis CRE : pixCreate_cps RT.
Hypothesis DES : pixDestroy_cps RT.
Hypothesis CMD : pixcmapDeserialize_cps RT.
Hypothesis SETC : pixSetColormap_cps RT.
Hypothesis VAL : pixcmapIsValid_cps RT.
Variables (Σ : rts RT) (PMc : Model -> Prop) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (usp lo : Z) (m : mem)
          (QF : config -> Prop) (fr : Z) (dp n : Z) (ras : list Z).

Theorem deser_tail_ok_0 :
  (forall rdes, In rdes DESER_DESTROY_RAS -> deser_ctx RT Σ PMc ra s0 usp lo m dp n ras rdes) ->
  (forall p k, In (p, k) (rt_live RT Σ) -> 0 < k) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  deser_epi_stmt_0 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr ->
  deser_cut0_stmt_0 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr dp n.
Proof using AF RC GP LSE RERR HDR CRE DES CMD SETC VAL.
  intros CTX LVP SECB EPI.
  assert (R1 : In 0x90944 DESER_DESTROY_RAS) by (unfold DESER_DESTROY_RAS; cbn [In]; tauto).
  assert (R4 : In 0x90b58 DESER_DESTROY_RAS) by (unfold DESER_DESTROY_RAS; cbn [In]; tauto).
  assert (R23 : forall rdes, In rdes [0x909a8; 0x90b18] -> In rdes DESER_DESTROY_RAS)
    by (intros rdes Hr; unfold DESER_DESTROY_RAS; cbn [In] in Hr |- *; tauto).
  apply (deser_cut0_ok_0 RT AF RC GP LSE RERR HDR DES Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr dp n ras (CTX _ R1) EPI).
  apply (deser_cut1_ok_0 RT AF RC GP RERR CRE DES CMD SETC Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr dp n ras
           (fun rdes Hr => CTX rdes (R23 rdes Hr)) LVP SECB EPI).
  exact (deser_cut2_ok_0 RT AF RC GP RERR DES VAL Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr dp n ras (CTX _ R4) EPI).
Qed.

Theorem deser_tail_ok_16 :
  (forall rdes, In rdes DESER_DESTROY_RAS -> deser_ctx RT Σ PMc ra s0 usp lo m dp n ras rdes) ->
  (forall p k, In (p, k) (rt_live RT Σ) -> 0 < k) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  deser_epi_stmt_16 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr ->
  deser_cut0_stmt_16 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr dp n.
Proof using AF RC GP LSE RERR HDR CRE DES CMD SETC VAL.
  intros CTX LVP SECB EPI.
  assert (R1 : In 0x90944 DESER_DESTROY_RAS) by (unfold DESER_DESTROY_RAS; cbn [In]; tauto).
  assert (R4 : In 0x90b58 DESER_DESTROY_RAS) by (unfold DESER_DESTROY_RAS; cbn [In]; tauto).
  assert (R23 : forall rdes, In rdes [0x909a8; 0x90b18] -> In rdes DESER_DESTROY_RAS)
    by (intros rdes Hr; unfold DESER_DESTROY_RAS; cbn [In] in Hr |- *; tauto).
  apply (deser_cut0_ok_16 RT AF RC GP LSE RERR HDR DES Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr dp n ras (CTX _ R1) EPI).
  apply (deser_cut1_ok_16 RT AF RC GP RERR CRE DES CMD SETC Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr dp n ras
           (fun rdes Hr => CTX rdes (R23 rdes Hr)) LVP SECB EPI).
  exact (deser_cut2_ok_16 RT AF RC GP RERR DES VAL Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr dp n ras (CTX _ R4) EPI).
Qed.

Theorem deser_front2_ok_0 :
  (forall rdes, In rdes DESER_DESTROY_RAS -> deser_ctx RT Σ PMc ra s0 usp lo m dp n ras rdes) ->
  (forall p k, In (p, k) (rt_live RT Σ) -> 0 < k) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  deser_epi_stmt_0 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr ->
  deser_cutm1_stmt_0 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr dp n.
Proof using AF RC GP LSE RERR HDR CRE DES CMD SETC VAL.
  intros CTX LVP SECB EPI.
  assert (R1 : In 0x90944 DESER_DESTROY_RAS) by (unfold DESER_DESTROY_RAS; cbn [In]; tauto).
  apply (deser_cutm1_ok_0 RT AF RC GP RERR Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr dp n ras 0x90944 (CTX _ R1) EPI).
  exact (deser_tail_ok_0 CTX LVP SECB EPI).
Qed.

Theorem deser_front2_ok_16 :
  (forall rdes, In rdes DESER_DESTROY_RAS -> deser_ctx RT Σ PMc ra s0 usp lo m dp n ras rdes) ->
  (forall p k, In (p, k) (rt_live RT Σ) -> 0 < k) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  deser_epi_stmt_16 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr ->
  deser_cutm1_stmt_16 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr dp n.
Proof using AF RC GP LSE RERR HDR CRE DES CMD SETC VAL.
  intros CTX LVP SECB EPI.
  assert (R1 : In 0x90944 DESER_DESTROY_RAS) by (unfold DESER_DESTROY_RAS; cbn [In]; tauto).
  apply (deser_cutm1_ok_16 RT AF RC GP RERR Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr dp n ras 0x90944 (CTX _ R1) EPI).
  exact (deser_tail_ok_16 CTX LVP SECB EPI).
Qed.
End TAIL.
