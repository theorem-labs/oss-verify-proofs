(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Bytes Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsImgSh AsIface AsIface5 AsIface6 AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AsTRList.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import X8Kit X8SRKit XL_mutex XL_cond X8_asio_stmt_alloc X8_asio_stmt_reg X8_asio_stmt_reg2 X8_asio_stmt_use X8_asio_stmt_cfg X8_asio_stmt_sched.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition ASCHED_CTOR_STACK : Z := 176 + ACONFIG_GET_STACK.     (* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Definition sched_hdr0 (ioc : Z) : svch := mkSVC AVP_SCHED 0 0 ioc 0 0.
Definition ASchedCells (m : mem) (S ioc : Z) : Prop :=
  exists j50 jm j109 je jt j219,
     rw_cells bsegs m S (SvcHdrCells (sched_hdr0 ioc))
  /\ rw_cells bsegs m (S + O_SCH_ONE_THREAD) [CB 2 [b8 0; b8 0]; CB 6 j50]
  /\ rw_cells bsegs m (S + O_SCH_MUTEX) [CB 8 jm]
  /\ APMutex m (S + O_SCH_PMUTEX) 0
  /\ rw_cells bsegs m (S + O_SCH_SPIN) [C4 (wz 0); CB 1 [b8 1]; CB 3 j109]
  /\ rw_cells bsegs m (S + O_SCH_EVENT) [CB 8 je]
  /\ APCond m (S + O_SCH_COND) CLOCK_MONOTONIC
  /\ rw_cells bsegs m (S + O_SCH_EVSTATE)
       [C8 (wz 0); C8 (wz 0); C8 (wz P_A_SCHED_GET_DEFAULT_TASK); C8 (wz 0); C8 (wz 0); C4 (wz 0); CB 4 jt;
        CB 3 [b8 1; b8 0; b8 0]; CB 5 j219; C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz u64max); C8 (wz u64max); C8 (wz 0)].

(* [comment removed for export] *)
Definition cfg_elt (ioc cfgb : Z) : svce := mkSE cfgb (cfg_hdr ioc) ATI_NAME_CONFIG.

Section W.
  Variable H : asr.

(* [comment removed for export] *)
Definition asc_pure (S ioc regb cfgb lo shi : Z) (sp tp ra : word) : Prop :=
  rblock_range S NEWSZ_SCH /\ (S + NEWSZ_SCH + 16 <= as_FSB H \/ as_FSB H + AFS_SIZE <= S - 16)
  /\ 0 < ioc /\ (ioc + 8) mod 8 = 0 /\ aapp (ioc + 8) 8
  /\ (cfgb + NEWSZ_CFG <= regb \/ regb + NEWSZ_REG <= cfgb)
  /\ (S + NEWSZ_SCH <= regb \/ regb + NEWSZ_REG <= S) /\ (S + NEWSZ_SCH <= cfgb \/ cfgb + NEWSZ_CFG <= S)
  /\ (ioc + 16 <= S \/ S + NEWSZ_SCH <= ioc + 8) /\ (ioc + 16 <= regb \/ regb + NEWSZ_REG <= ioc + 8)
  /\ tp = Z_to_bv 64 ATP /\ bv_unsigned sp mod 16 = 0 /\ bv_unsigned sp <= 0x7fffffffffff
  /\ lo + ASCHED_CTOR_STACK <= bv_unsigned sp /\ aceil <= lo /\ bv_unsigned ra mod 2 = 0 /\ bv_unsigned sp <= shi.

(* [comment removed for export] *)
Definition asc_fs (LF : list fframe) (S ioc regb cfgb : Z) : Prop :=
  fsobj H LF S NEWSZ_SCH /\ fsobj H LF (ioc + 8) 8 /\ fsobj H LF regb NEWSZ_REG /\ fsobj H LF cfgb NEWSZ_CFG.

(* [comment removed for export] *)
Definition asc_inv (LB : list block) (m : mem) (ioc regb cfgb : Z) (errv : word) : Prop :=
  ro_cells bsegs m (ioc + 8) [C8 (wz regb)] /\ accessible m (ioc + 8) 8
  /\ ARegistry LB m regb ioc cfgb 0 /\ AConfigSvc LB m cfgb (cfg_hdr ioc)
  /\ AXStatics2 m /\ ACanaryReads m /\ acanary m
  /\ rw_cells bsegs m AERRNO [C4 errv].

Definition asc_W (lo : Z) (sp : word) (S regb : Z) : list (Z * Z) :=
  [(lo, bv_unsigned sp); (S, S + SZ_SCH); (regb + O_REG_MUTEX, regb + O_REG_MUTEX + 40); (AERRNO, AERRNO + 4)]%Z.

Definition asched_ctor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB : list block) (LF : list fframe) (S ioc regb cfgb lo shi : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (XS : list (Z * Z)),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ Forall (fs_scratch H LF) XS
    /\ munch (asc_W lo sp S regb ++ XS) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ ASchedCells m' S ioc /\ addressable m' S NEWSZ_SCH
    /\ asc_inv LB m' ioc regb cfgb (wz 0)
    /\ as_RHEAP H s LB m'
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi.

(* [comment removed for export] *)
Definition asched_ctor_stmt : Prop :=
  forall (s : as_St H) (S ioc regb cfgb lo shi : Z) (LB : list block) (LF : list fframe)
    ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (errv : word) (junk : list byte),
  F = bvmap_empty -> fc = Z_to_bv 32 0 ->
  rw_cells bsegs m S [CB 272 junk] -> addressable m S NEWSZ_SCH -> (exists p, In (p, S, NEWSZ_SCH) LB) ->
  asc_pure S ioc regb cfgb lo shi sp tp ra -> asc_fs LF S ioc regb cfgb -> asc_inv LB m ioc regb cfgb errv ->
  as_RHEAP H s LB m ->
  stk bsegs m lo (bv_unsigned sp) ->
  mem_inv bsegs m ->
  (* [comment removed for export] *)
  ACONST m -> as_RFS H LF m -> (length LF + 1 < AFS_MAXLIVE)%nat -> stack0 m lo shi ->
  evt bsegs (asched_ctor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF S ioc regb cfgb lo shi m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz S) (wz ioc) (wz 0) (wz P_A_SCHED_GET_DEFAULT_TASK) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_A_SCHED_CTOR) fc None m (seg_rom bsegs)).

End W.
End HCW.
