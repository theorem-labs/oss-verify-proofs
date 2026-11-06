(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow R_sizeclass.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface R_cache_defs R_prim_defs R_glue_defs R_thread R_sec_defs R_depot_defs R_quar_defs R_qrec_defs R_qrecycle R_qdorec R_qcbrec R_mmapordie RT_state RT_rep RT_freestate RT_drain_defs RT_drain_ldefs.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow R_sizeclass.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_cache_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_prim_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_glue_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_thread.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_sec_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_depot_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_quar_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_qrec_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_qrecycle.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_qdorec.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_qcbrec.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_mmapordie.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_state.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_rep.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_freestate.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_drain_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_drain_ldefs.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Cuts.
Variables (p : dlp) (j : list byte) (b : Z) (ents : list (Z * Z)) (i : nat) (rest : list batch) (Σk : rtsA) (k : nat) (s : secst).
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation C := (dl_usp p - 2288).
#[local] Notation T := (l_T (lay (dl_Σ0 p))).

(* [comment removed for export] *)
Definition ds_loopmem (m : mem) : Prop :=
  (exists G, wmono_out G (dl_m0 p) m /\ dl_gone p G)
  /\ rt_pres (live Σ0) (frames Σ0) (C + 32) (dl_m0 p) m
  /\ drec_frame m C j (T + 208) (usp - 2128) (Z_to_bv 64 0x3462c) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p)
       (dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p)
  /\ qcache_rep m C rest /\ qbatch m b (qfirst rest) ents.

(* [comment removed for export] *)
Definition svc_mun : machine_state -> Prop :=
  fun ms => exists (t0' t1' t2' a2' a3' a4' a5' a6' t3' t4' t5' t6' : word) (m' : mem),
    ms = MSsvc (uod_regs (Z_to_bv 64 0x348e8) (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0' t1' t2' (s_mb s) (smsz (s_n s))
                 a2' a3' a4' a5' a6' (Z_to_bv 64 864648) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
                 (Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
                 (dl_s10 p) (dl_s11 p) t3' t4' t5' t6')
               (dl_F p) (Z_to_bv 64 sec_munmap_ecall) (Z_to_bv 64 215) (dl_fc p) None m' (seg_rom bsegs)
    /\ ARTc (recs Σk k) m' /\ mem_inv bsegs m'
    /\ uod_frame m' (Z_to_bv 64 (C - 112)) (Z_to_bv 64 0x348e8) (Z_to_bv 64 C) (Z_to_bv 64 INST) (Z_to_bv 64 864024)
    /\ stk bsegs m' (dl_lo p) (C - 112 - 48)
    /\ ds_loopmem m'.

End Cuts.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow RT_iface R_sizeclass R_cache_defs R_prim_defs R_glue_defs R_thread
  R_sec_defs R_depot_defs R_quar_defs R_qrec_defs R_qrecycle R_qdorec R_qcbrec R_mmapordie
  RT_state RT_rep RT_freestate RT_drain_defs RT_drain_ldefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Cuts.
Variables (p : dlp) (j : list byte) (b : Z) (ents : list (Z * Z)) (i : nat) (rest : list batch) (Σk : rtsA) (k : nat) (s : secst).
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation C := (dl_usp p - 2288).
#[local] Notation T := (l_T (lay (dl_Σ0 p))).

(* [comment removed for export] *)
Definition ds_loopmem (m : mem) : Prop :=
  (exists G, wmono_out G (dl_m0 p) m /\ dl_gone p G)
  /\ rt_pres (live Σ0) (frames Σ0) (C + 32) (dl_m0 p) m
  /\ drec_frame m C j (T + 208) (usp - 2128) (Z_to_bv 64 0x34744) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p)
       (dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p)
  /\ qcache_rep m C rest /\ qbatch m b (qfirst rest) ents.

(* [comment removed for export] *)
Definition svc_mun : machine_state -> Prop :=
  fun ms => exists (t0' t1' t2' a2' a3' a4' a5' a6' t3' t4' t5' t6' : word) (m' : mem),
    ms = MSsvc (uod_regs (Z_to_bv 64 0x34a00) (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0' t1' t2' (s_mb s) (smsz (s_n s))
                 a2' a3' a4' a5' a6' (Z_to_bv 64 810376) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
                 (Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
                 (dl_s10 p) (dl_s11 p) t3' t4' t5' t6')
               (dl_F p) (Z_to_bv 64 sec_munmap_ecall) (Z_to_bv 64 215) (dl_fc p) None m' (seg_rom asegs)
    /\ ARTc (recs Σk k) m' /\ mem_inv asegs m'
    /\ uod_frame m' (Z_to_bv 64 (C - 112)) (Z_to_bv 64 0x34a00) (Z_to_bv 64 C) (Z_to_bv 64 INST) (Z_to_bv 64 809752)
    /\ stk asegs m' (dl_lo p) (C - 112 - 48)
    /\ ds_loopmem m'.

End Cuts.
