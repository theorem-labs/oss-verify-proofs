(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require TP_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Bytes Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsImgSh AsIface AsIface5 AsIface6 AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AsTRList.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import X8Kit X8SRKit X8_asio_stmt_alloc X8_asio_stmt_reg2 X8_asio_stmt_sched3 X8_asio_stmt_sched4
     X8_stream_stmt X8_stream_stmt3 X8_dss_stmt.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition P_B_EXEC_CTX_DTOR : Z := 0xa6b34.    (* [comment removed for export] *)
Definition P_B_DESTROY_AT_REG : Z := 0xb9b54.   (* [comment removed for export] *)
Definition P_B_ECTX_RET_SHUT : Z := 0xa6be4.   (* [comment removed for export] *)
Definition P_B_ECTX_RET_DSV  : Z := 0xa6c6c.   (* [comment removed for export] *)
Definition P_B_ECTX_RET_DAT  : Z := 0xa6cac.   (* [comment removed for export] *)
Definition P_B_ECTX_RET_ATD  : Z := 0xa6cbc.   (* [comment removed for export] *)
Definition P_B_ECTX_RET_AID  : Z := 0xa6d00.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition AECTX_STACK : Z := 80 + ADSS_STACK.

(* [comment removed for export] *)
Definition frobj (LF : list fframe) (A n : Z) : Prop :=
  exists f, In f LF /\ ff_addr f <= A /\ A + n <= ff_addr f + fsz (ff_class f).

Lemma frobj_aobj : forall LB LF A n, frobj LF A n -> aobj LB LF A n.
Proof. intros LB LF A n K. right. exact K. Qed.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

(* [comment removed for export] *)
Definition ectx_LB (LB : list block) (pv pq pva ps pc pr pa : bptr) : list block :=
  as_lb_remove H pa (as_lb_remove H pr (as_lb_remove H pc (as_lb_remove H ps
    (as_lb_remove H pv (as_lb_remove H pq (as_lb_remove H pva LB)))))).

(* [comment removed for export] *)
Definition ectx_X (v q va schedb cfgb regb allocb : Z) : list (Z * Z) :=
  blkX v NEWSZ_SSVC ++ blkX q SZ_SPCI_IMPL ++ blkX va 8 ++ blkX schedb NEWSZ_SCH ++ blkX cfgb NEWSZ_CFG
  ++ blkX regb NEWSZ_REG ++ blkX allocb SZ_ALLOCIMPL.

(* [comment removed for export] *)
Definition ectx_cost : Z := dos_cost H + as_Cf H NEWSZ_SCH + as_Cf H NEWSZ_CFG + as_Cf H NEWSZ_REG + as_Cf H SZ_ALLOCIMPL.

Definition exec_ctx_dtor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB : list block) (LF : list fframe) (ioc allocb regb v q va schedb cfgb lo B shi : Z)
    (pv pq pva ps pc pr pa : bptr) (errv : word) (m : mem) (mo : Model) : config -> Prop :=
  fun cf => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : as_St H) (XS : list (Z * Z)),
    as_VIS H s' (cfg_ms cf) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ as_AKREL H s' cf /\ as_MPRES H mo (cfg_model cf)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (errno_addr tp) [C4 errv] /\ as_rauxv_ok H m' B
    /\ as_RHEAP H s' (ectx_LB LB pv pq pva ps pc pr pa) m'
    /\ rw_cells bsegs m' ioc [C8 (wz allocb); C8 (wz regb)]
    /\ AXStatics2 m'
    /\ Forall (fs_scratch H LF) XS
    /\ xpres H (ectx_LB LB pv pq pva ps pc pr pa) (bv_unsigned sp) (ectx_X v q va schedb cfgb regb allocb ++ XS) m m'
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
    /\ as_AL H s' >= as_AL H s - ectx_cost.

Definition exec_ctx_dtor_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (ioc allocb regb v q va schedb cfgb sh0 lo B shi : Z)
         (pv pq pva ps pc pr pa : bptr) (errv : word),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_B_EXEC_CTX_DTOR) fc None m (seg_rom bsegs) ->
    a0 = Z_to_bv 64 ioc ->
    (* [comment removed for export] *)
    rw_cells bsegs m ioc [C8 (wz allocb); C8 (wz regb)] -> frobj LF ioc 16 -> ioc mod 8 = 0 -> accessible m ioc 16 ->
    (* [comment removed for export] *)
    ARegistry LB m regb ioc v 0 ->
    AStreamSvc LB m v (mkSVC AVP_SSVC 0 AG_ID_SSVC ioc schedb P_A_DESTROY_ALLOC_SSVC) q ->
    AImplBlockC LB m q (mkIMPL (mkSPC AVP_SPCI_IMPL 1 1 1) 0 va [] 1) ->
    AScheduler LB m schedb (mkSCH (sched_hdr ioc cfgb) 0 0 sh0) ->
    AConfigSvc LB m cfgb (cfg_hdr ioc) ->
    AAllocImpl LB m allocb ->
    In (pv, v, NEWSZ_SSVC) LB -> In (pq, q, SZ_SPCI_IMPL) LB -> In (pva, va, 8) LB ->
    In (ps, schedb, NEWSZ_SCH) LB -> In (pc, cfgb, NEWSZ_CFG) LB -> In (pr, regb, NEWSZ_REG) LB -> In (pa, allocb, SZ_ALLOCIMPL) LB ->
    (* [comment removed for export] *)
    pv <> pr ->
    AXStatics2 m ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk bsegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AECTX_STACK ->
    rw_cells bsegs m (errno_addr tp) [C4 errv] -> mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
    bv_unsigned ra mod 2 = 0 ->
    (* [comment removed for export] *)
    bv_unsigned sp mod 16 = 0 ->
    as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat -> ACONST m -> stack0 m lo shi -> bv_unsigned sp <= shi ->
    ectx_cost <= as_AL H s ->
    as_SR H (exec_ctx_dtor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF ioc allocb regb v q va schedb cfgb lo B shi
                                pv pq pva ps pc pr pa errv m mo)
      (mkCfg msF mo).

End HCW.
