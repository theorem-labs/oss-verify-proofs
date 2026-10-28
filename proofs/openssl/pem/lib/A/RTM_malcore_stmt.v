(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs R_cache_defs R_thread R_asan_defs R_allocate1 RT_state RT_rep RT_maltail RT_malcore_stmt RTM_maltail.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition core_entry_al64 (Σ : rtsA) (B Bt : Z) (gp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (n : Z)
    (m : mem) : machine_state :=
  MS (mkR (Z_to_bv 64 0x19af0c) (Z_to_bv 64 (B + -144)) gp (Z_to_bv 64 tpA) t0 t1 t2
          (Z_to_bv 64 (Z.b2z (from_primary n))) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 (l_T (lay Σ) + 208))
          (Z_to_bv 64 (needed2 n + 64)) (Z_to_bv 64 8) a4 a5 a6 a7 (Z_to_bv 64 64) (Z_to_bv 64 (needed2 n + 64))
          (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 Bt) (Z_to_bv 64 (0 + - (64)))
          (Z_to_bv 64 63) (Z_to_bv 64 (l_T (lay Σ))) (Z_to_bv 64 1) t3 t4 t5 t6)
     F (Z_to_bv 64 0x19f4cc) fc None m (seg_rom asegs).

Definition core_case_al64 (P : Z -> Prop) : Prop :=
  forall (Σ : rtsA) (PMc : Model -> Prop) (mX : mem) (B Bt : Z)
         (raA gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (tr : list Z) (tb : list word) (j0 : list byte),
  fdfs_only PMc -> mat_stable PMc -> P n -> 1 <= n <= 0x8000000 ->
  rz_size n mod 64 = 0 -> ClassID (needed2 n + 64) = ClassID (needed2 n) -> ClassSize (ClassID (needed2 n)) mod 64 = 0 ->
  needed2 n + 64 <= 64512 ->
  Z.of_nat (length (live Σ)) < LIVE_MAX -> mcost n <= credit Σ ->
  ART_A Σ mX -> mem_inv asegs mX ->
  stk asegs mX lo (B + -144) -> l_ACEIL (lay Σ) <= lo -> lo + 0x1000 <= B + -144 -> B + 2144 <= USTACK_TOP -> B mod 16 = 0 ->
  B <= Bt /\ Bt + 2144 <= USTACK_TOP ->
  In tr (T_MAIN (l_cg (lay Σ))) -> (1 <= length tr <= 30)%nat -> trc_cells Bt tr mX tb ->
  af_cells_g64 B raA s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A mX j0 ->
  cps asegs (ASTA RTA Σ PMc (eq (core_entry_al64 Σ B Bt gp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc n mX)))
            (core_post_g Σ PMc B raA gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A n lo mX).

Definition core_stmt_prim_al64 : Prop := core_case_al64 (fun n => n <= 64512).

