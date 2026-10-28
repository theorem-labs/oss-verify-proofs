(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_prim_defs R_glue_defs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_thread. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_sec_defs R_depot_defs R_quar_defs R_qrec_defs R_qrecycle R_qdorec R_qcbrec R_mmapordie RT_state RT_rep RT_freestate RT_drain_defs RT_drain_ldefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.
Section Cuts.
Variables (p : dlp) (j : list byte) (b : Z) (ents : list (Z * Z)) (i : nat) (rest : list batch) (Σk : rtsA) (k : nat) (s : secst).
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation C := (dl_usp p - 2288).
#[local] Notation T := (l_T (lay (dl_Σ0 p))).

Definition ds_loopmem (m : mem) : Prop :=
  (exists G, wmono_out G (dl_m0 p) m /\ dl_gone p G)
  /\ rt_pres (live Σ0) (frames Σ0) (C + 32) (dl_m0 p) m
  /\ drec_frame m C j (T + 208) (usp - 2128) (Z_to_bv 64 0x5d648) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p)
       (dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p)
  /\ qcache_rep m C rest /\ qbatch m b (qfirst rest) ents.

Definition svc_mun : machine_state -> Prop :=
  fun ms => exists (t0' t1' t2' a2' a3' a4' a5' a6' t3' t4' t5' t6' : word) (m' : mem),
    ms = MSsvc (uod_regs (Z_to_bv 64 0x5d904) (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0' t1' t2' (s_mb s) (smsz (s_n s))
                 a2' a3' a4' a5' a6' (Z_to_bv 64 1509512) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
                 (Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
                 (dl_s10 p) (dl_s11 p) t3' t4' t5' t6')
               (dl_F p) (Z_to_bv 64 sec_munmap_ecall) (Z_to_bv 64 215) (dl_fc p) None m' (seg_rom asegs)
    /\ ARTc (recs Σk k) m' /\ mem_inv asegs m'
    /\ uod_frame m' (Z_to_bv 64 (C - 112)) (Z_to_bv 64 0x5d904) (Z_to_bv 64 C) (Z_to_bv 64 INST) (Z_to_bv 64 1508888)
    /\ stk asegs m' (dl_lo p) (C - 112 - 48)
    /\ ds_loopmem m'.

End Cuts.

End GWIN.
