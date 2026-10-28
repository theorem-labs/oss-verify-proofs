(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_G_kit Fz_ckit Fz_M_malloc Fz_M_zalloc Fz_env Fz_G_CRYPTO_calloc Fz_G_OPENSSL_LH_new Fz_G_OPENSSL_LH_set_thunks Fz_I2_pdefns.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section PDefnsD.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_LHN : OPENSSL_LH_new_stmt RT.

Definition ossl_property_defns_new_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x150 + 16 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_pdefns (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) PDEFNS_SITES PDEFNS_CALLS ->
  Z.of_nat (length (rt_live RT Σ)) + 2 <= LIVE_MAX -> mcost 104 + mcost 128 <= rt_credit RT Σ ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pdefns m)))
    (fun c => exists (Σ' : rts RT) (lh B : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 lh) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ wr_at asegs m' lh 104 /\ acc asegs m' lh 104 /\ wr_at asegs m' B 128 /\ acc asegs m' B 128
           /\ rw_cells asegs m' lh (pdefns_cells B)
           /\ rw_cells asegs m' B [CB 128 (repeat (Z_to_bv 8 0) 128)]) c
       /\ rt_live RT Σ' = (B, 128) :: (lh, 104) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - (mcost 104 + mcost 128)
       /\ 0 < lh /\ lh mod 16 = 0 /\ lh + 104 < USTACK_TOP /\ 0 < B /\ B mod 16 = 0 /\ B + 128 < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem ossl_property_defns_new_cps : ossl_property_defns_new_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
    FDO MST Etp ART0 MI0 CALL HSTK CTX UWC CGH Hlen Hcr ENV.
  eapply cps_conseq; [exact (pdefns_cps RT GOBJ AF AFP C_LHN Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
                                 FDO MST Etp ART0 MI0 CALL HSTK CTX UWC CGH Hlen Hcr ENV) | intros c Hc; exact Hc |].
  intros c (Σ' & lh & B & HA & LV & FRS & SP & CR & CG & P0 & P16 & PU & Q0 & Q16 & QU). exists Σ', lh, B.
  repeat (split; [assumption|]). exact CG.
Qed.
End PDefnsD.
