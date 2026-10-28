(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface D_defs R_sizeclass R_cache_defs R_thread R_asan_defs R_allocate1 RT_state RT_rep RT_maltail.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition core_entry (Σ : rtsA) (B : Z) (gp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (n : Z)
    (m : mem) : machine_state :=
  MS (mkR (Z_to_bv 64 0x195ec8) (Z_to_bv 64 (B + -144)) gp (Z_to_bv 64 tpA) t0 t1 t2
          (Z_to_bv 64 (Z.b2z (from_primary n))) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 (l_T (lay Σ) + 208))
          (Z_to_bv 64 (needed2 n)) (Z_to_bv 64 8) a4 a5 a6 a7 (Z_to_bv 64 8) (Z_to_bv 64 (needed2 n))
          (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 (0 + - (8)))
          (Z_to_bv 64 7) (Z_to_bv 64 (l_T (lay Σ))) (Z_to_bv 64 1) t3 t4 t5 t6)
     F (Z_to_bv 64 0x19a488) fc None m (seg_rom bsegs).

(* [comment removed for export] *)
Definition core_post (Σ : rtsA) (PMc : Model -> Prop) (B : Z) (gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A : word)
    (n lo : Z) (mX : mem) : config -> Prop :=
  fun cf => exists (Σ' : rtsA) (p : Z),
    ASTA RTA Σ' PMc (fun ms => exists m', ret_st (Z_to_bv 64 0x195bf8) (Z_to_bv 64 (B + -16)) gp (Z_to_bv 64 tpA)
                                             s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A (Z_to_bv 64 p) m' ms
        /\ ART_A Σ' m' /\ mem_inv bsegs m' /\ wmono bsegs mX m' /\ stk bsegs m' lo (B + -16)
        /\ rt_pres (live Σ) (frames Σ) (B + -16) mX m' /\ wr_at bsegs m' p n /\ acc bsegs m' p n) cf
    /\ live Σ' = (p, n) :: live Σ /\ frames Σ' = frames Σ /\ rtA_sp0 Σ' = rtA_sp0 Σ /\ credit Σ' = credit Σ - mcost n
    /\ 0 < p /\ p mod 16 = 0 /\ p + n < USTACK_TOP.

(* [comment removed for export] *)
Definition core_case (P : Z -> Prop) : Prop :=
  forall (Σ : rtsA) (PMc : Model -> Prop) (mX : mem) (B : Z)
         (gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (tr : list Z) (tb : list word) (j0 : list byte),
  fdfs_only PMc -> mat_stable PMc -> P n -> 1 <= n <= 0x8000000 ->
  Z.of_nat (length (live Σ)) < LIVE_MAX -> mcost n <= credit Σ ->
  ART_A Σ mX -> mem_inv bsegs mX ->
  stk bsegs mX lo (B + -144) -> l_ACEIL (lay Σ) <= lo -> lo + 0x1000 <= B + -144 -> B + 2144 <= USTACK_TOP -> B mod 16 = 0 ->
  In tr T_MAIN -> (1 <= length tr <= TR_MAX)%nat -> trc_cells B tr mX tb ->
  af_cells B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A mX j0 ->
  cps bsegs (ASTA RTA Σ PMc (eq (core_entry Σ B gp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc n mX)))
            (core_post Σ PMc B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A n lo mX).

Definition core_stmt_prim : Prop := core_case (fun n => n <= 64512).
Definition core_stmt_sec : Prop := core_case (fun n => 64512 < n).
