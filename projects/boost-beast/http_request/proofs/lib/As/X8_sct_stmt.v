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
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsIface AsIface5 AsIface6 AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AsTRList.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import X8Kit X8SRKit X8_asio_stmt_alloc X8_asio_stmt_reg X8_asio_stmt_reg2 X8_asio_stmt_sched3 X8_cobj
     X8_stream_stmt X8_stream_stmt2.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_SC_RET_MI   : Z := 0xa43dc.   (* [comment removed for export] *)
Definition P_SC_RET_DES  : Z := 0xa4404.   (* [comment removed for export] *)
Definition P_SC_RET_MS   : Z := 0xa4414.   (* [comment removed for export] *)
Definition P_SC_RET_AR1  : Z := 0xa441c.   (* [comment removed for export] *)
Definition P_SC_RET_AR2  : Z := 0xa4428.   (* [comment removed for export] *)
Definition P_SC_RET_PREP : Z := 0xa4434.   (* [comment removed for export] *)
Definition P_SC_RET_CPY  : Z := 0xa4450.   (* [comment removed for export] *)
Definition SC_DESCR : Z := 0x22f92.        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ASTREAM_CTOR_STACK : Z := 144 + AMAKE_IMPL_STACK.

(* [comment removed for export] *)
Definition stream_fb (N A : Z) : fbv := if N =? 0 then FB_empty else mkFB A A (A + N) (A + N) (A + N).
Definition st_LB (N : Z) (p5 : bptr) (A : Z) (LB4 : list block) : list block := if N =? 0 then LB4 else (p5, A, N) :: LB4.

Section HCW.
  Context {HCEIL : HeapCeil}.
Section W.
  Variable H : asr.

Definition stream_ctor_cost (N : Z) : Z := make_impl_cost H + as_Cm H N.

Definition stream_ctor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB : list block) (LF : list fframe) (bs ioc D N allocb regb cfgb schedb lo B shi : Z) (ds : list byte)
    (m : mem) (mo : Model) : config -> Prop :=
  fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H)
                  (p1 : bptr) (v : Z) (p2 : bptr) (q : Z) (p3 : bptr) (stb : Z) (p4 : bptr) (va : Z) (p5 : bptr) (A : Z) (XS : list (Z * Z)),
    as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
    /\ rblock_range v NEWSZ_SSVC /\ rblock_range q SZ_SPCI_IMPL /\ rblock_range stb SZ_SPCI_STATE /\ rblock_range va 8
    /\ (1 <= N -> rblock_range A N /\ (A + N <= stb \/ stb + SZ_SPCI_STATE <= A))
    /\ as_RHEAP H s' (st_LB N p5 A (mi_LB p1 v p2 q p3 stb p4 va LB)) m'
    /\ rw_cells asegs m' bs (BasicStreamCells stb)
    /\ ARegistry (st_LB N p5 A (mi_LB p1 v p2 q p3 stb p4 va LB)) m' regb ioc v 0
    /\ AStreamSvc (st_LB N p5 A (mi_LB p1 v p2 q p3 stb p4 va LB)) m' v (mkSVC AVP_SSVC 0 AG_ID_SSVC ioc schedb P_A_DESTROY_ALLOC_SSVC) q
    /\ AImplBlock (st_LB N p5 A (mi_LB p1 v p2 q p3 stb p4 va LB)) m' q (impl_after va stb)
    /\ AStateBlock (st_LB N p5 A (mi_LB p1 v p2 q p3 stb p4 va LB)) m' stb ioc q
                   (mkST (mkSPC AVP_SPCI_STATE 1 1 1) 0 (stream_fb N A) STREAM_OK 0 0) ds
    /\ AAllocImpl (st_LB N p5 A (mi_LB p1 v p2 q p3 stb p4 va LB)) m' allocb
    /\ AConfigSvc (st_LB N p5 A (mi_LB p1 v p2 q p3 stb p4 va LB)) m' cfgb (cfg_hdr ioc)
    /\ AScheduler (st_LB N p5 A (mi_LB p1 v p2 q p3 stb p4 va LB)) m' schedb (mkSCH (sched_hdr ioc cfgb) 0 0 0)
    /\ AXStatics2 m'
    /\ Forall (fs_scratch H LF) XS
    /\ xpres H LB (bv_unsigned sp) ([(bs, bs + SZ_BS); (regb, regb + NEWSZ_REG)]%Z ++ XS) m m'
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
    /\ as_AL H s' >= as_AL H s - stream_ctor_cost N.

Definition stream_ctor_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (bs ioc D N allocb regb cfgb schedb lo B shi : Z) (errv : word) (ds jbs : list byte),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_STREAM_CTOR) fc None m (seg_rom asegs) ->
    a0 = Z_to_bv 64 bs -> a1 = Z_to_bv 64 ioc -> a2 = Z_to_bv 64 D -> a3 = Z_to_bv 64 N ->
    (* [comment removed for export] *)
    rw_cells asegs m bs [CB 32 jbs] -> cobj LB LF (bv_unsigned sp) shi bs SZ_BS -> bs mod 8 = 0 -> accessible m bs SZ_BS ->
    (* [comment removed for export] *)
    ro_cells asegs m ioc (IoCtxCells allocb regb schedb) -> aobj LB LF ioc 24 -> ioc mod 8 = 0 -> accessible m ioc 24 -> 0 < ioc ->
    (bs + SZ_BS <= ioc \/ ioc + 24 <= bs) ->
    ARegistry LB m regb ioc schedb 0 -> AScheduler LB m schedb (mkSCH (sched_hdr ioc cfgb) 0 0 0) -> AConfigSvc LB m cfgb (cfg_hdr ioc) ->
    (ioc + 24 <= regb \/ regb + NEWSZ_REG <= ioc) -> (bs + SZ_BS <= regb \/ regb + NEWSZ_REG <= bs) ->
    (bs + SZ_BS <= schedb \/ schedb + NEWSZ_SCH <= bs) -> (bs + SZ_BS <= cfgb \/ cfgb + NEWSZ_CFG <= bs) ->
    AAllocImpl LB m allocb -> (bs + SZ_BS <= allocb \/ allocb + SZ_ALLOCIMPL <= bs) -> AXStatics2 m ->
    (* [comment removed for export] *)
    bytes_at asegs m D ds -> Z.of_nat (length ds) = N -> N < 2^26 -> D < 2^64 ->
    (1 <= N -> exists pD, In (pD, D, N) LB) -> (1 <= N -> addressable m D N) ->
    (1 <= N -> D + N <= bs \/ bs + SZ_BS <= D) -> (1 <= N -> D + N <= regb \/ regb + NEWSZ_REG <= D) ->
    (* [comment removed for export] *)
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    lb_bytes LB + MAKE_IMPL_LIVE + N <= as_LIVE_MAX H -> Z.of_nat (length LB) + 5 <= as_LIVE_CNT_MAX H ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    (* [comment removed for export] *)
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ASTREAM_CTOR_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
    bv_unsigned ra mod 2 = 0 ->
    (* [comment removed for export] *)
    bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= 0x7fffffffffff ->
    as_RFS H LF m -> (length LF + 1 < AFS_MAXLIVE)%nat -> ACONST m ->
    stack0 m lo shi -> bv_unsigned sp + 64 <= shi ->
    stream_ctor_cost N <= as_AL H s ->
    as_SR H (stream_ctor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF bs ioc D N allocb regb cfgb schedb lo B shi ds m mo)
      (mkCfg msF mo).

End W.
End HCW.
