(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Mem Frame Cells Step Arr Exec RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_defs R_cache_defs R_thread R_asan_defs R_allocate1 RT_state RT_rep RT_maltail RT_caltail.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ccore_entry (Σ : rtsA) (B : Z) (gp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (n : Z)
    (m : mem) : machine_state :=
  MS (mkR (Z_to_bv 64 0x19bfbc) (Z_to_bv 64 (B + -184)) gp (Z_to_bv 64 tpA) t0 t1 t2
          (Z_to_bv 64 (Z.b2z (from_primary n))) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 (l_T (lay Σ) + 208))
          (Z_to_bv 64 (needed2 n)) (Z_to_bv 64 8) a4 a5 a6 a7 (Z_to_bv 64 8) (Z_to_bv 64 (needed2 n))
          (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 (0 + - (8)))
          (Z_to_bv 64 7) (Z_to_bv 64 (l_T (lay Σ))) (Z_to_bv 64 1) t3 t4 t5 t6)
     F (Z_to_bv 64 0x1a057c) fc None m (seg_rom ctasegs).

(* [comment removed for export] *)
Definition ccore_post (Σ : rtsA) (PMc : Model -> Prop) (B : Z) (gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A : word)
    (n lo : Z) (mX : mem) : config -> Prop :=
  fun cf => exists (Σ' : rtsA) (p : Z),
    ASTA RTA Σ' PMc (fun ms => exists m', ret_st (Z_to_bv 64 0x19c6f8) (Z_to_bv 64 (B + -56)) gp (Z_to_bv 64 tpA)
                                             s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A (Z_to_bv 64 p) m' ms
        /\ ART_A Σ' m' /\ mem_inv ctasegs m' /\ wmono ctasegs mX m' /\ stk ctasegs m' lo (B + -56)
        /\ rt_pres (live Σ) (frames Σ) (B + -56) mX m' /\ wr_at ctasegs m' p n /\ acc ctasegs m' p n) cf
    /\ live Σ' = (p, n) :: live Σ /\ frames Σ' = frames Σ /\ rtA_sp0 Σ' = rtA_sp0 Σ /\ credit Σ' = credit Σ - mcost n
    /\ 0 < p /\ p mod 16 = 0 /\ p + n < USTACK_TOP.

(* [comment removed for export] *)
Definition core_stmt_calloc : Prop :=
  forall (Σ : rtsA) (PMc : Model -> Prop) (mX : mem) (B : Z)
         (gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (tr : list Z) (tb : list word) (j0 : list byte),
  fdfs_only PMc -> mat_stable PMc -> 1 <= n <= 64512 ->
  live_room (live Σ) n -> mcost n <= credit Σ ->      (* [comment removed for export] *)
  ART_A Σ mX -> mem_inv ctasegs mX ->
  stk ctasegs mX lo (B + -184) -> l_ACEIL (lay Σ) <= lo -> lo + 0x1000 <= B + -184 -> B + 2144 <= USTACK_TOP -> B mod 16 = 8 ->
  In tr T_MAIN -> (1 <= length tr <= TR_MAX)%nat -> trc_cells B tr mX tb ->
  caf_cells B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A mX j0 ->
  cps ctasegs (ASTA RTA Σ PMc (eq (ccore_entry Σ B gp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc n mX)))
            (ccore_post Σ PMc B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A n lo mX).
