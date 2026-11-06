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
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import X8Kit X8SRKit X8_asio_stmt_alloc X8_asio_stmt_reg.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition P_A_CONFIG_MAKE : Z := 0xa6da8.    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition AMAKE_SVC_CONFIG_STACK : Z := 112 + AALLOCATE_STACK.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ACONFIG_MAKE_STACK : Z := 16 + AMAKE_SVC_CONFIG_STACK.

(* [comment removed for export] *)
Definition cfg_hdr (ioc : Z) : svch := mkSVC AVP_CONFIG_SVC AL_TYPEID_CONFIG 0 ioc 0 P_A_DESTROY_ALLOC_CONFIG.

Section HCW.
  Context {HCEIL : HeapCeil}.
Section W.
  Variable H : asr.

Definition make_svc_config_cost : Z := allocate_cost H SZ_CFG.

(* [comment removed for export] *)
Definition make_svc_config_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB : list block) (LF : list fframe) (r ioc allocb lo B shi : Z) (m : mem) (mo : Model) : config -> Prop :=
  fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (p : bptr) (A : Z) (XS : list (Z * Z)),
    as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
    /\ rblock_range A NEWSZ_CFG /\ as_RHEAP H s' ((p, A, NEWSZ_CFG) :: LB) m'
    /\ AConfigSvc ((p, A, NEWSZ_CFG) :: LB) m' A (cfg_hdr ioc)
    /\ ARegistry ((p, A, NEWSZ_CFG) :: LB) m' r ioc A 0
    /\ AAllocImpl ((p, A, NEWSZ_CFG) :: LB) m' allocb
    /\ AXStatics2 m'
    /\ Forall (fs_scratch H LF) XS
    /\ xpres H LB (bv_unsigned sp) ([(r, r + NEWSZ_REG)]%Z ++ XS) m m'
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
    /\ as_AL H s' >= as_AL H s - make_svc_config_cost.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition make_svc_config_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (r hintp ioc allocb lo B shi : Z) (errv : word),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_MAKE_SVC_CONFIG) fc None m (seg_rom bsegs) ->
    a0 = Z_to_bv 64 r -> a1 = Z_to_bv 64 hintp ->
    ARegistry LB m r ioc 0 0 ->
    ro_cells bsegs m ioc [C8 (wz allocb)] -> 0 < ioc -> ioc mod 8 = 0 -> ioc + 8 <= aceil -> accessible m ioc 8 ->
    AAllocImpl LB m allocb -> AXStatics2 m ->
    ro_cells bsegs m hintp [C4 (wz 4294967295)] -> bv_unsigned sp <= hintp -> hintp + 4 <= shi ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    lb_bytes LB + NEWSZ_CFG <= as_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= as_LIVE_CNT_MAX H ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk bsegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AMAKE_SVC_CONFIG_STACK ->
    rw_cells bsegs m (errno_addr tp) [C4 errv] -> mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
    bv_unsigned ra mod 2 = 0 ->
    (* [comment removed for export] *)
    bv_unsigned sp mod 16 = 0 ->
    as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat -> ACONST m ->
    stack0 m lo shi -> bv_unsigned sp + 64 <= shi ->
    make_svc_config_cost <= as_AL H s ->
    as_SR H (make_svc_config_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF r ioc allocb lo B shi m mo)
      (mkCfg msF mo).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition config_make_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (cfh r ioc allocb lo B shi : Z) (errv : word),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_CONFIG_MAKE) fc None m (seg_rom bsegs) ->
    a0 = Z_to_bv 64 cfh -> a1 = Z_to_bv 64 ioc ->
    ro_cells bsegs m (cfh + 8) [C4 (wz 4294967295)] -> 0 < cfh -> cfh mod 8 = 0 -> cfh + 16 <= aceil -> accessible m (cfh + 8) 8 ->
    ro_cells bsegs m ioc [C8 (wz allocb); C8 (wz r)] -> 0 < ioc -> ioc mod 8 = 0 -> ioc + 16 <= aceil -> accessible m ioc 16 ->
    ARegistry LB m r ioc 0 0 ->
    AAllocImpl LB m allocb -> AXStatics2 m ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    lb_bytes LB + NEWSZ_CFG <= as_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= as_LIVE_CNT_MAX H ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk bsegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ACONFIG_MAKE_STACK ->
    rw_cells bsegs m (errno_addr tp) [C4 errv] -> mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
    bv_unsigned ra mod 2 = 0 ->
    (* [comment removed for export] *)
    bv_unsigned sp mod 16 = 0 ->
    as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat -> ACONST m ->
    stack0 m lo shi -> bv_unsigned sp + 64 <= shi ->
    make_svc_config_cost <= as_AL H s ->
    as_SR H (make_svc_config_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF r ioc allocb lo B shi m mo)
      (mkCfg msF mo).

End W.
End HCW.
