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
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface AsIface5 AsIface6 AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AsTRList.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import X8Kit X8SRKit X8_A_leaves2 XL_mutex XL_cond X8_asio_stmt_alloc X8_asio_stmt_sp X8_asio_stmt_sp2 X8_asio_stmt_reg X8_asio_stmt_use X8_cobj X8_S_place X8_stream_stmt.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AMAKE_SHARED_STATE_STACK : Z := 176 + ASHCOUNT_CTOR_STACK.
(* [comment removed for export] *)
Definition AMAKE_IMPL_STACK : Z := 96 + ADUSC_STACK.
(* [comment removed for export] *)
Definition MAKE_IMPL_LIVE : Z := NEWSZ_SSVC + SZ_SPCI_IMPL + SZ_SPCI_STATE + 8.

Definition state_init : statev := mkST (mkSPC AVP_SPCI_STATE 1 1 1) 0 FB_empty STREAM_OK 0 0.
Definition impl_after (va stb : Z) : implv := mkIMPL (mkSPC AVP_SPCI_IMPL 1 2 1) 0 va [stb + O_SPC_STORAGE] 1.
Definition mi_LB (p1 : bptr) (v : Z) (p2 : bptr) (q : Z) (p3 : bptr) (stb : Z) (p4 : bptr) (va : Z) (LB : list block) : list block :=
  (p4, va, 8) :: (p3, stb, SZ_SPCI_STATE) :: (p2, q, SZ_SPCI_IMPL) :: (p1, v, NEWSZ_SSVC) :: LB.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section W1.
  Variable H : asr.

Definition make_shared_state_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB : list block) (LF : list fframe) (R implb ioc lo B shi : Z) (ivp iu ii : Z) (ij7 : list byte) (m : mem) (mo : Model)
    : config -> Prop :=
  fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (p : bptr) (q : Z) (XS : list (Z * Z)),
    as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
    /\ rblock_range q SZ_SPCI_STATE /\ as_RHEAP H s' ((p, q, SZ_SPCI_STATE) :: LB) m'
    /\ rw_cells bsegs m' R [C8 (wz (q + O_SPC_STORAGE)); C8 (wz q)]
    /\ AStateBlock ((p, q, SZ_SPCI_STATE) :: LB) m' q ioc implb state_init []
    /\ rw_cells bsegs m' implb (SpcHdrCells (mkSPC ivp iu 2 ii) ij7)
    /\ AXStatics2 m'
    /\ Forall (fs_scratch H LF) XS
    /\ xpres H LB (bv_unsigned sp) ([(R, R + 16); (implb + 12, implb + 16)]%Z ++ XS) m m'
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
    /\ as_AL H s' >= as_AL H s - as_Cm H SZ_SPCI_STATE.

Definition make_shared_state_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (R EX SPP FCP implb ioc lo B shi : Z) (pi : bptr) (ivp iu ii : Z)
         (errv : word) (jr j16 ij7 : list byte),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_MAKE_SHARED_STATE) fc None m (seg_rom bsegs) ->
    a0 = Z_to_bv 64 R -> a1 = Z_to_bv 64 EX -> a2 = Z_to_bv 64 SPP -> a3 = Z_to_bv 64 FCP ->
    rw_cells bsegs m R [CB 16 jr] -> cobj LB LF (bv_unsigned sp) shi R 16 -> R mod 8 = 0 -> accessible m R 16 ->
    ro_cells bsegs m EX (AnyExecCells EX ioc j16) -> aobj LB LF EX 56 -> EX mod 8 = 0 -> accessible m EX 56 -> 0 < EX ->
    0 <= ioc < 2^64 ->
    ro_cells bsegs m SPP [C8 (wz (implb + 32)); C8 (wz implb)] -> aobj LB LF SPP 16 -> SPP mod 8 = 0 -> accessible m SPP 16 ->
    ro_cells bsegs m FCP [C8 (wz 0)] -> bv_unsigned sp <= FCP -> FCP + 8 <= shi -> FCP mod 8 = 0 ->
    rw_cells bsegs m implb (SpcHdrCells (mkSPC ivp iu 1 ii) ij7) -> spc_ok (mkSPC ivp iu 1 ii) -> In (pi, implb, SZ_SPCI_IMPL) LB ->
    accessible m implb SZ_SPCI_IMPL ->
    (R + 16 <= EX \/ EX + 56 <= R) -> (R + 16 <= SPP \/ SPP + 16 <= R) -> (R + 16 <= implb \/ implb + SZ_SPCI_IMPL <= R) ->
    (R + 16 <= FCP \/ FCP + 8 <= R) ->
    AXStatics2 m ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    lb_bytes LB + SZ_SPCI_STATE <= as_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= as_LIVE_CNT_MAX H ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk bsegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AMAKE_SHARED_STATE_STACK ->
    rw_cells bsegs m (errno_addr tp) [C4 errv] -> mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
    bv_unsigned ra mod 2 = 0 ->
    (* [comment removed for export] *)
    bv_unsigned sp mod 16 = 0 -> athr_cells m ->
    as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat -> ACONST m ->
    stack0 m lo shi -> bv_unsigned sp + 64 <= shi ->
    as_Cm H SZ_SPCI_STATE <= as_AL H s ->
    as_SR H (make_shared_state_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF R implb ioc lo B shi ivp iu ii ij7 m mo)
      (mkCfg msF mo).
End W1.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section W2.
  Variable H : asr.

Definition make_impl_cost : Z := dusc_cost H + as_Cm H SZ_SPCI_STATE + as_Cm H 8.

Definition make_impl_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB : list block) (LF : list fframe) (R ioc regb first allocb lo B shi : Z) (m : mem) (mo : Model) : config -> Prop :=
  fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H)
                  (p1 : bptr) (v : Z) (p2 : bptr) (q : Z) (p3 : bptr) (stb : Z) (p4 : bptr) (va : Z) (XS : list (Z * Z)),
    as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
    /\ rw_cells bsegs m' R [C8 (wz (stb + O_SPC_STORAGE)); C8 (wz stb)]
    /\ as_RHEAP H s' (mi_LB p1 v p2 q p3 stb p4 va LB) m'
    /\ rblock_range v NEWSZ_SSVC /\ rblock_range q SZ_SPCI_IMPL /\ rblock_range stb SZ_SPCI_STATE /\ rblock_range va 8
    /\ ARegistry (mi_LB p1 v p2 q p3 stb p4 va LB) m' regb ioc v 0
    /\ AStreamSvc (mi_LB p1 v p2 q p3 stb p4 va LB) m' v (mkSVC AVP_SSVC 0 AG_ID_SSVC ioc first P_A_DESTROY_ALLOC_SSVC) q
    /\ AImplBlock (mi_LB p1 v p2 q p3 stb p4 va LB) m' q (impl_after va stb)
    /\ AStateBlock (mi_LB p1 v p2 q p3 stb p4 va LB) m' stb ioc q state_init []
    /\ AAllocImpl (mi_LB p1 v p2 q p3 stb p4 va LB) m' allocb
    /\ AXStatics2 m'
    /\ Forall (fs_scratch H LF) XS
    /\ xpres H LB (bv_unsigned sp) ([(R, R + 16); (regb, regb + NEWSZ_REG)]%Z ++ XS) m m'
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
    /\ as_AL H s' >= as_AL H s - make_impl_cost.

Definition make_impl_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (L : list svce)
         (R EX ioc regb first allocb schedb lo B shi : Z) (errv : word) (jr j16 : list byte),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_SSVC_MAKE_IMPL) fc None m (seg_rom bsegs) ->
    a0 = Z_to_bv 64 R -> a1 = Z_to_bv 64 EX -> a2 = Z_to_bv 64 0 ->
    (* [comment removed for export] *)
    rw_cells bsegs m R [CB 16 jr] -> cobj LB LF (bv_unsigned sp) shi R 16 -> R mod 8 = 0 -> accessible m R 16 ->
    (* [comment removed for export] *)
    rw_cells bsegs m EX (AnyExecCells EX ioc j16) -> aobj LB LF EX 56 -> EX mod 8 = 0 -> accessible m EX 56 -> 0 < EX ->
    (R + 16 <= EX \/ EX + 56 <= R) ->
    (* [comment removed for export] *)
    ro_cells bsegs m ioc (IoCtxCells allocb regb schedb) -> aobj LB LF ioc 24 -> ioc mod 8 = 0 -> accessible m ioc 24 -> 0 < ioc ->
    (R + 16 <= ioc \/ ioc + 24 <= R) ->
    ARegistry LB m regb ioc first 0 -> (ioc + 24 <= regb \/ regb + NEWSZ_REG <= ioc) -> (R + 16 <= regb \/ regb + NEWSZ_REG <= R) ->
    (EX + 56 <= regb \/ regb + NEWSZ_REG <= EX) ->     (* [comment removed for export] *)
    ASvcChain m first L -> Forall (fun e => keys_match 0 AG_ID_SSVC 0 e = false) L ->
    Forall (fun e => aobj LB LF (se_addr e) 48 /\ (se_addr e + 48 <= regb \/ regb + SZ_REG <= se_addr e) /\ ati_client e) L ->
    AAllocImpl LB m allocb -> (R + 16 <= allocb \/ allocb + SZ_ALLOCIMPL <= R) -> AXStatics2 m ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    lb_bytes LB + MAKE_IMPL_LIVE <= as_LIVE_MAX H -> Z.of_nat (length LB) + 4 <= as_LIVE_CNT_MAX H ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk bsegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AMAKE_IMPL_STACK ->
    rw_cells bsegs m (errno_addr tp) [C4 errv] -> mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
    bv_unsigned ra mod 2 = 0 ->
    (* [comment removed for export] *)
    bv_unsigned sp mod 16 = 0 -> athr_cells m ->
    as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat -> ACONST m ->
    stack0 m lo shi -> bv_unsigned sp + 64 <= shi ->
    make_impl_cost <= as_AL H s ->
    as_SR H (make_impl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF R ioc regb first allocb lo B shi m mo)
      (mkCfg msF mo).
End W2.

End HCW.
