(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout Th_mutex I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_G_kit Fz_ckit Fz_M_malloc Fz_env.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Export Fz_I2_ppis.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PPI_COST : Z := 8 + Fz_I2_ppis.PPI_COST.
Lemma PPI_COST_nonneg : 0 <= PPI_COST.
Proof. pose proof Fz_I2_ppis.PPI_COST_nonneg as H. unfold PPI_COST. lia. Qed.

Section PropertyParseInit.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition ossl_property_parse_init_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (ps pk pl1 pb1 pl2 pb2 pq1 pq2 : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 PPI_CTX -> tp = Z_to_bv 64 0xba3ef0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x400 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_property_parse_init (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) PPI_SITES PPI_CALLS ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 19 <= LIVE_MAX -> PPI_COST <= rt_credit RT Σ ->
  Forall (fun x => 0 < snd x) (rt_live RT Σ) ->
  cl_env m lb canary ->
  rw_cells asegs m CTX_PSD [C8 (Z_to_bv 64 ps)] ->
  In (ps, 48) (rt_live RT Σ) -> In (pk, 40) (rt_live RT Σ) -> In (pl1, 104) (rt_live RT Σ) -> In (pb1, 128) (rt_live RT Σ) ->
  In (pl2, 104) (rt_live RT Σ) -> In (pb2, 128) (rt_live RT Σ) -> In (pq1, 56) (rt_live RT Σ) -> In (pq2, 56) (rt_live RT Σ) ->
  ps mod 16 = 0 -> pk mod 16 = 0 -> pl1 mod 16 = 0 -> pb1 mod 16 = 0 -> pl2 mod 16 = 0 -> pb2 mod 16 = 0 -> pq1 mod 16 = 0 -> pq2 mod 16 = 0 ->
  pl1 <> pl2 -> pb1 <> pb2 -> pq1 <> pq2 ->
  rw_cells asegs m ps [C8 (Z_to_bv 64 pk); C8 (Z_to_bv 64 pl1); C8 (Z_to_bv 64 pl2); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 pq1); C8 (Z_to_bv 64 pq2)] ->
  rw_cells asegs m pk (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
  rw_cells asegs m pl1 [C8 (Z_to_bv 64 pb1); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)] ->
  rw_cells asegs m pb1 [CB 128 (repeat (Z_to_bv 8 0) 128)] ->
  rw_cells asegs m pl2 [C8 (Z_to_bv 64 pb2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)] ->
  rw_cells asegs m pb2 [CB 128 (repeat (Z_to_bv 8 0) 128)] ->
  rw_cells asegs m pq1 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 2146284); C8 (Z_to_bv 64 2146368); C8 (Z_to_bv 64 2146328)] ->
  rw_cells asegs m pq2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 2146284); C8 (Z_to_bv 64 2146368); C8 (Z_to_bv 64 2146328)] ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_property_parse_init m)))
    (fun c => exists (Σ' : rts RT) (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 : Z),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp)
                 [(ps, ps + 48); (pk, pk + 40); (pl1, pl1 + 104); (pb1, pb1 + 128); (pl2, pl2 + 104); (pb2, pb2 + 128); (pq1, pq1 + 56); (pq2, pq2 + 56);
                  (G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
           /\ cl_env m' (Z_to_bv 8 1) canary) c
       /\ rt_live RT Σ' = (a18, 24) :: (a17, 18) :: (a16, 24) :: (a15, 32) :: (a14, 19) :: (a13, 24) :: (a12, 25) :: (a11, 24) :: (a10, 48) :: (a9, 21) :: (a8, 24) :: (a7, 22) :: (a6, 24) :: (a5, 20) :: (a4, 24) :: (a3, 23) :: (a2, 24) :: (a1, 24) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - PPI_COST
       /\ 0 < a1 /\ a1 mod 16 = 0 /\ a1 + 24 < USTACK_TOP /\ 0 < a2 /\ a2 mod 16 = 0 /\ a2 + 24 < USTACK_TOP /\ 0 < a3 /\ a3 mod 16 = 0 /\ a3 + 23 < USTACK_TOP /\ 0 < a4 /\ a4 mod 16 = 0 /\ a4 + 24 < USTACK_TOP /\ 0 < a5 /\ a5 mod 16 = 0 /\ a5 + 20 < USTACK_TOP /\ 0 < a6 /\ a6 mod 16 = 0 /\ a6 + 24 < USTACK_TOP /\ 0 < a7 /\ a7 mod 16 = 0 /\ a7 + 22 < USTACK_TOP /\ 0 < a8 /\ a8 mod 16 = 0 /\ a8 + 24 < USTACK_TOP /\ 0 < a9 /\ a9 mod 16 = 0 /\ a9 + 21 < USTACK_TOP /\ 0 < a10 /\ a10 mod 16 = 0 /\ a10 + 48 < USTACK_TOP /\ 0 < a11 /\ a11 mod 16 = 0 /\ a11 + 24 < USTACK_TOP /\ 0 < a12 /\ a12 mod 16 = 0 /\ a12 + 25 < USTACK_TOP /\ 0 < a13 /\ a13 mod 16 = 0 /\ a13 + 24 < USTACK_TOP /\ 0 < a14 /\ a14 mod 16 = 0 /\ a14 + 19 < USTACK_TOP /\ 0 < a15 /\ a15 mod 16 = 0 /\ a15 + 32 < USTACK_TOP /\ 0 < a16 /\ a16 mod 16 = 0 /\ a16 + 24 < USTACK_TOP /\ 0 < a17 /\ a17 mod 16 = 0 /\ a17 + 18 < USTACK_TOP /\ 0 < a18 /\ a18 mod 16 = 0 /\ a18 + 24 < USTACK_TOP
       /\ rt_cg RT Σ' = rt_cg RT Σ).
End PropertyParseInit.
