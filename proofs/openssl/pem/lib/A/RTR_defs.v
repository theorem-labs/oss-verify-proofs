(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_quar_defs R_qput R_qenqueue R_asan_free R_prim_kit RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2 RT_freestmt RT_freeC RT_freeD RT_freeF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition enq_post_g (CF : mem -> Prop) (retw q0 q1 q2 q3 q4 q5 : word) (Bt : Z) (Σ2 : rtsA) (live0 : list (Z * Z)) (frames0 : list (Z * nat)) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' t3 t4 t5 t6 : word) (m' : mem),
    ms = enq_ret_st (bv_unsigned sp) (l_T (lay Σ2)) gp ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m'
    /\ ARTc Σ2 m' /\ rt_wfx Σ2 /\ rt_count Σ2 /\ mem_inv asegs m' /\ wmono asegs m m' /\ stk asegs m' lo (bv_unsigned sp + -2208)
    /\ rt_pres live0 frames0 (bv_unsigned sp) m m'
    /\ CF m'
    /\ qput_frame m' (bv_unsigned sp + -2208) (Z_to_bv 64 (l_T (lay Σ2) + 208)) (Z_to_bv 64 Bt) retw
         q0 q1 q2 q3 q4 q5 s6.

