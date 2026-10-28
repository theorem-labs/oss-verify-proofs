(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Mem Frame Cells Step Arr Exec RzCPS MState. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface R_cache_defs R_prim_defs R_glue_defs R_thread R_depot_defs R_quar_defs R_qrec_defs R_qrecycle R_qdorec R_qcbrec R_cdealloc RT_state RT_rep RT_freestate RT_drain_defs RT_drain_led RT_drain_start RT_drain_ldefs RT_refreeG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Vocab.
Variable p : dlp.
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation C := (dl_usp p - 2288).
#[local] Notation T := (l_T (lay (dl_Σ0 p))).
#[local] Notation SB := (l_SB (lay (dl_Σ0 p))).

(* [comment removed for export] *)
Definition dl_gone_r (G : list ivl) : Prop :=
  Forall (fun r => forall a, fst r <= a < snd r -> ~ aclient (live Σ0) (frames Σ0) (C + 32) a /\ ~ (dl_lo p <= a < C + 32)) G.

(* [comment removed for export] *)
Definition dl_mem_r (j : list byte) (Σk : rtsA) (rest : list batch) (m : mem) : Prop :=
  ARTc Σk m /\ mem_inv ctasegs m /\ stk ctasegs m (dl_lo p) (C - 112) /\ (exists G, wmono_out G (dl_m0 p) m /\ dl_gone_r G)
  /\ rt_pres (live Σ0) (frames Σ0) (C + 32) (dl_m0 p) m
  /\ drec_frame m C j (T + 208) (usp - 2056) (Z_to_bv 64 0x19de04) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p)
       (dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p)
  /\ qcache_rep m C rest.

(* [comment removed for export] *)
Definition dl_sig_r (Σk : rtsA) : Prop :=
  lay Σk = lay Σ0 /\ live Σk = live Σ0 /\ frames Σk = frames Σ0 /\ credit Σk = credit Σ0 /\ ql Σk = [] /\ ca_init Σk = true.

(* [comment removed for export] *)
Definition dl_Q_r (j : list byte) (b : Z) (ents : list (Z * Z)) (i : nat) (rest : list batch) (Σk : rtsA) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
    ms = MS (mkR (Z_to_bv 64 0x19e0c0) (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST)
                 (Z_to_bv 64 (C - 104)) (Z_to_bv 64 (fst (nth i ents (0%Z, 0%Z)))) a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 6744600) (Z_to_bv 64 6745224) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
                 (Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
                 (dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
            (dl_F p) (Z_to_bv 64 qcbrec_entry) (dl_fc p) None m (seg_rom ctasegs)
    /\ dl_mem_r j Σk rest m /\ qbatch m b (qfirst rest) ents.

(* [comment removed for export] *)
Definition dl_N_r (j : list byte) (b : Z) (ents : list (Z * Z)) (i : nat) (rest : list batch) (Σk : rtsA) : machine_state -> Prop :=
  fun ms => exists (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
    ms = MS (mkR ra0 (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 6744600) (Z_to_bv 64 6745224) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
                 (Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
                 (dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
            (dl_F p) (Z_to_bv 64 0x19e0c0) (dl_fc p) None m (seg_rom ctasegs)
    /\ dl_mem_r j Σk rest m /\ qbatch m b (qfirst rest) ents.

(* [comment removed for export] *)
Definition dl_D_r (j : list byte) (b : Z) (ents : list (Z * Z)) (rest : list batch) (Σk : rtsA) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a4 a5 a6 a7 s6 s7 s8 s9 t3 t4 t5 t6 : word) (m : mem),
    ms = MS (mkR (Z_to_bv 64 0x19e0f8) (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST)
                 (Z_to_bv 64 (T + 208)) (Z_to_bv 64 INST) (Z_to_bv 64 24) (Z_to_bv 64 b) a4 a5 a6 a7
                 (Z_to_bv 64 6744600) (Z_to_bv 64 6745224) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) s6 s7 s8 s9
                 (dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
            (dl_F p) (Z_to_bv 64 cdealloc_entry) (dl_fc p) None m (seg_rom ctasegs)
    /\ dl_mem_r j Σk rest m /\ qbatch m b (qfirst rest) ents.

(* [comment removed for export] *)
Definition dl_B_r (j : list byte) (rest : list batch) (Σk : rtsA) : machine_state -> Prop :=
  fun ms => exists (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 t3 t4 t5 t6 : word) (m : mem),
    ms = MS (mkR ra0 (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 6744600) (Z_to_bv 64 6745224) s4 (Z_to_bv 64 (2^37)) s6 s7 s8 s9 (dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
            (dl_F p) (Z_to_bv 64 0x19e0f8) (dl_fc p) None m (seg_rom ctasegs)
    /\ dl_mem_r j Σk rest m.

(* [comment removed for export] *)
Definition dl_R_r (Σk : rtsA) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
    ms = MS (mkR (Z_to_bv 64 0x19de04) (Z_to_bv 64 C) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (dl_r0 p) (dl_r1 p) a0 a1 a2 a3 a4 a5 a6 a7
                 (dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p) (dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
            (dl_F p) (ret_pc (Z_to_bv 64 0x19de04)) (dl_fc p) None m (seg_rom ctasegs)
    /\ ARTc Σk m /\ mem_inv ctasegs m /\ stk ctasegs m (dl_lo p) C /\ (exists G, wmono_out G (dl_m0 p) m /\ dl_gone_r G)
    /\ rt_pres (live Σ0) (frames Σ0) (C + 32) (dl_m0 p) m /\ qcache_rep m C [].

(* [comment removed for export] *)
Definition dl_fin_r : config -> Prop :=
  fun cf => exists Σ' : rtsA, ASTA RTA Σ' (dl_PMc p) (dl_R_r Σ') cf /\ rt_wfP Σ' [] /\ dl_sig_r Σ'.

End Vocab.
