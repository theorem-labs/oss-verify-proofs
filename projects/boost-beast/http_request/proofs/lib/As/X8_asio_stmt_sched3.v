(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Bytes Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsImgSh AsIface AsIface5 AsIface6 AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AsTRList.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import X8Kit X8SRKit X8_asio_stmt_alloc X8_asio_stmt_reg X8_asio_stmt_reg2 X8_asio_stmt_sched2.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition AMAKE_SVC_SCHED_STACK : Z := 128 + AALLOCATE_STACK.

(* [comment removed for export] *)
Definition ainframe (LF : list fframe) (O n : Z) : Prop := exists f, In f LF /\ ff_addr f <= O /\ O + n <= ff_addr f + fsz (ff_class f).

(* [comment removed for export] *)
Definition sched_hdr (ioc cfgb : Z) : svch := mkSVC AVP_SCHED AL_TYPEID_SCHED 0 ioc cfgb P_A_DESTROY_ALLOC_SCHED.

Section HCW.
  Context {HCEIL : HeapCeil}.
Section W.
  Variable H : asr.

Definition make_svc_sched_cost : Z := allocate_cost H SZ_SCH.

Definition make_svc_sched_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB : list block) (LF : list fframe) (r ioc cfgb allocb lo B shi : Z) (m : mem) (mo : Model) : config -> Prop :=
  fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : as_St H) (p : bptr) (S : Z) (XS : list (Z * Z)),
    as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 (wz 0)] /\ as_rauxv_ok H m' B
    /\ rblock_range S NEWSZ_SCH /\ as_RHEAP H s' ((p, S, NEWSZ_SCH) :: LB) m'
    /\ AScheduler ((p, S, NEWSZ_SCH) :: LB) m' S (mkSCH (sched_hdr ioc cfgb) 0 0 0)
    /\ ARegistry ((p, S, NEWSZ_SCH) :: LB) m' r ioc S 0
    /\ AConfigSvc ((p, S, NEWSZ_SCH) :: LB) m' cfgb (cfg_hdr ioc)
    /\ AAllocImpl ((p, S, NEWSZ_SCH) :: LB) m' allocb
    /\ AXStatics2 m' /\ ACanaryReads m' /\ acanary m'
    /\ Forall (fs_scratch H LF) XS
    /\ xpres H LB (bv_unsigned sp) ([(r, r + NEWSZ_REG); (AERRNO, AERRNO + 4)]%Z ++ XS) m m'
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
    /\ as_AL H s' >= as_AL H s - make_svc_sched_cost.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition make_svc_sched_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (r ownp ioc cfgb allocb lo B shi : Z) (errv : word),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_MAKE_SVC_SCHED) fc None m (seg_rom asegs) ->
    a0 = Z_to_bv 64 r -> a1 = Z_to_bv 64 ownp -> F = bvmap_empty -> fc = Z_to_bv 32 0 ->
    (* [comment removed for export] *)
    ARegistry LB m r ioc cfgb 0 -> AConfigSvc LB m cfgb (cfg_hdr ioc) ->
    (* [comment removed for export] *)
    ro_cells asegs m ioc [C8 (wz allocb); C8 (wz r)] -> ioc mod 8 = 0 -> accessible m ioc 16 -> ainframe LF ioc 16 ->
    (* [comment removed for export] *)
    ro_cells asegs m ownp [CB 1 [b8 0]] -> bv_unsigned sp <= ownp -> ownp + 1 <= shi ->
    AAllocImpl LB m allocb -> AXStatics2 m -> ACanaryReads m -> acanary m ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    lb_bytes LB + NEWSZ_SCH <= as_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= as_LIVE_CNT_MAX H ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AMAKE_SVC_SCHED_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
    bv_unsigned ra mod 2 = 0 ->
    (* [comment removed for export] *)
    bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= 0x7fffffffffff ->
    as_RFS H LF m -> (length LF + 1 < AFS_MAXLIVE)%nat -> ACONST m ->
    stack0 m lo shi -> bv_unsigned sp + 64 <= shi ->
    make_svc_sched_cost <= as_AL H s ->
    as_SR H (make_svc_sched_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF r ioc cfgb allocb lo B shi m mo)
      (mkCfg msF mo).

End W.
End HCW.
