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
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import X8Kit X8SRKit XL_mutex X8_asio_stmt_alloc X8_asio_stmt_sp X8_asio_stmt_sp2 X8_asio_stmt_reg.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition ADUS_STACK : Z := 112 + 32 + MUTEX_UNLOCK_STACK.     (* [comment removed for export] *)
Definition ADUSC_STACK : Z := 112 + ACREATE_SSVC_STACK.

(* [comment removed for export] *)
Definition adusf_W (lo : Z) (sp : word) (r : Z) : list (Z * Z) := [(lo, bv_unsigned sp); (r + O_REG_MUTEX, r + O_REG_MUTEX + 40)]%Z.

(* [comment removed for export] *)
Definition ati_client (e : svce) : Prop :=
  sv_ti (se_hdr e) <> 0 -> 0x119000 <= sv_ti (se_hdr e) + 8 /\ sv_ti (se_hdr e) + 16 <= 0x121468.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition do_use_service_found_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (LB : list block) (r owner first fsv lo shi : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz fsv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (adusf_W lo sp r) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ ARegistry LB m' r owner first 0
    /\ ACONST m' /\ stack0 m' lo shi.

Definition do_use_service_found_stmt : Prop :=
  forall (r K fsv lo shi : Z) (LB : list block) (L : list svce) (owner first kti kid kname : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  ARegistry LB m r owner first 0 ->
  ro_cells bsegs m K [C8 (wz kti); C8 (wz kid)] -> 0 <= kti < 2^64 -> 0 <= kid < 2^64 -> 0 <= kname < 2^64 ->
  (kti <> 0 -> ati_ok m kti kname) ->
  ASvcChain m first L -> find_svc kti kid kname L = fsv -> fsv <> 0 ->
  Forall (fun e => se_addr e + 48 <= r \/ r + SZ_REG <= se_addr e) L ->
  bv_unsigned sp <= K -> K + 16 <= shi -> K mod 8 = 0 ->
  stk bsegs m lo (bv_unsigned sp) -> lo + ADUS_STACK <= bv_unsigned sp -> aceil <= lo ->
  bv_unsigned ra mod 2 = 0 ->
  mem_inv bsegs m ->
  (* [comment removed for export] *)
  bv_unsigned sp mod 16 = 0 -> ACONST m -> stack0 m lo shi ->
  evt bsegs (do_use_service_found_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB r owner first fsv lo shi m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz r) (wz K) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_A_DO_USE_SERVICE) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section W.
  Variable H : asr.

Definition dusc_cost : Z := create_ssvc_cost H.

Definition do_use_service_create_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB : list block) (LF : list fframe) (r ctx own first kti kid allocb lo B shi : Z) (m : mem) (mo : Model) : config -> Prop :=
  fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (p1 : bptr) (v : Z) (p2 : bptr) (q : Z)
                  (XS : list (Z * Z)),
    as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
    /\ rblock_range v NEWSZ_SSVC /\ rblock_range q SZ_SPCI_IMPL
    /\ as_RHEAP H s' ((p2, q, SZ_SPCI_IMPL) :: (p1, v, NEWSZ_SSVC) :: LB) m'
    /\ ARegistry ((p2, q, SZ_SPCI_IMPL) :: (p1, v, NEWSZ_SSVC) :: LB) m' r ctx v 0
    /\ AStreamSvc ((p2, q, SZ_SPCI_IMPL) :: (p1, v, NEWSZ_SSVC) :: LB) m' v (mkSVC AVP_SSVC kti kid own first P_A_DESTROY_ALLOC_SSVC) q
    /\ AImplBlock ((p2, q, SZ_SPCI_IMPL) :: (p1, v, NEWSZ_SSVC) :: LB) m' q (mkIMPL (mkSPC AVP_SPCI_IMPL 1 1 1) 0 0 [] 0)
    /\ AAllocImpl ((p2, q, SZ_SPCI_IMPL) :: (p1, v, NEWSZ_SSVC) :: LB) m' allocb
    /\ AXStatics2 m'
    /\ Forall (fs_scratch H LF) XS
    /\ xpres H LB (bv_unsigned sp) ([(r, r + NEWSZ_REG)]%Z ++ XS) m m'
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
    /\ as_AL H s' >= as_AL H s - dusc_cost.

Definition do_use_service_create_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (L : list svce)
         (r K ctx own first kti kid kname allocb lo B shi : Z) (errv : word),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_DO_USE_SERVICE) fc None m (seg_rom bsegs) ->
    a0 = Z_to_bv 64 r -> a1 = Z_to_bv 64 K -> a2 = Z_to_bv 64 P_A_CREATE_SSVC -> a3 = Z_to_bv 64 own ->
    ARegistry LB m r ctx first 0 ->
    ro_cells bsegs m ctx [C8 (wz allocb)] -> 0 < ctx -> ctx mod 8 = 0 -> ctx + 8 <= aceil -> accessible m ctx 8 ->
    (ctx + 8 <= r \/ r + NEWSZ_REG <= ctx) ->
    0 <= own < 2^64 ->
    0 < own -> own mod 8 = 0 ->     (* [comment removed for export] *)
    AAllocImpl LB m allocb -> AXStatics2 m ->
    ro_cells bsegs m K [C8 (wz kti); C8 (wz kid)] -> bv_unsigned sp <= K -> K + 80 <= shi -> K mod 8 = 0 ->
    0 <= kti < 2^64 -> 0 <= kid < 2^64 -> 0 <= kname < 2^64 ->
    (kti <> 0 -> ati_ok m kti kname /\ kti + 16 <= 0x121468) ->
    ASvcChain m first L -> Forall (fun e => keys_match kti kid kname e = false) L ->
    Forall (fun e => aobj LB LF (se_addr e) 48 /\ (se_addr e + 48 <= r \/ r + SZ_REG <= se_addr e) /\ ati_client e) L ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    lb_bytes LB + NEWSZ_SSVC + SZ_SPCI_IMPL <= as_LIVE_MAX H -> Z.of_nat (length LB) + 2 <= as_LIVE_CNT_MAX H ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk bsegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ADUSC_STACK ->
    rw_cells bsegs m (errno_addr tp) [C4 errv] -> mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
    bv_unsigned ra mod 2 = 0 ->
    (* [comment removed for export] *)
    bv_unsigned sp mod 16 = 0 ->
    as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat -> ACONST m ->
    stack0 m lo shi -> bv_unsigned sp + 64 <= shi ->
    dusc_cost <= as_AL H s ->
    as_SR H (do_use_service_create_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF r ctx own first kti kid allocb lo B shi m mo)
      (mkCfg msF mo).

End W.
End HCW.
