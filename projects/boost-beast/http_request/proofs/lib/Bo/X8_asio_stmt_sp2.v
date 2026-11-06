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
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import X8SRKit X8_A_leaves2 X8_asio_stmt_alloc X8_asio_stmt_sp.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AANYEX_QUERY_STACK : Z := 112 + AFS_STACK.

Section HCW.
  Context {HCEIL : HeapCeil}.
Section W.
  Variable H : asr.

Definition aq_W (lo : Z) (sp : word) (ff fp : Z) : list (Z * Z) :=
  [(lo, bv_unsigned sp); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 128); (sh ff, sh ff + 16)]%Z.

Definition anyex_query_ctx_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (E ioc : Z) (j16 : list byte) (LF : list fframe) (lo shi : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (ff fp : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz ioc) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (aq_W lo sp ff fp) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' E (AnyExecCells E ioc j16)
    /\ fresh_frame H LF 1 ff fp /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi.

Definition anyex_query_ctx_stmt : Prop :=
  forall (E ioc lo shi : Z) (j16 : list byte) (LF : list fframe)
    ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  rw_cells bsegs m E (AnyExecCells E ioc j16) -> 0 <= ioc < 2^64 -> ioc mod 8 = 0 -> AXStatics2 m ->
  0 < ioc ->     (* [comment removed for export] *)
  stk bsegs m lo (bv_unsigned sp) -> lo + AANYEX_QUERY_STACK <= bv_unsigned sp -> aceil <= lo ->
  bv_unsigned ra mod 2 = 0 ->
  mem_inv bsegs m ->
  (* [comment removed for export] *)
  bv_unsigned sp mod 16 = 0 -> tp = Z_to_bv 64 ATP -> ACONST m -> athr_cells m ->
  as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat ->
  stack0 m lo shi -> bv_unsigned sp + 64 <= shi ->
  aapp E 56 -> fsobj H LF E 56 -> accessible m E 56 -> E mod 8 = 0 ->
  evt bsegs (anyex_query_ctx_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc E ioc j16 LF lo shi m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz E) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_A_ANYEX_QUERY_CONTEXT) fc None m (seg_rom bsegs)).

End W.
End HCW.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ACREATE_SSVC_STACK : Z := 32 + 48 + AALLOCATE_STACK.

Section HCW2.
  Context {HCEIL : HeapCeil}.
Section W2.
  Variable H : asr.

Definition ssvc_hdr0 (own : Z) : svch := mkSVC AVP_SSVC 0 0 own 0 P_A_DESTROY_ALLOC_SSVC.
Definition create_ssvc_cost : Z := allocate_cost H SZ_SSVC + as_Cm H SZ_SPCI_IMPL.

Definition create_ssvc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB : list block) (LF : list fframe) (own allocb lo B shi : Z) (m : mem) (mo : Model) : config -> Prop :=
  fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (p1 : bptr) (v : Z) (p2 : bptr) (q : Z) j7
                  (XS : list (Z * Z)),
    as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
    /\ rblock_range v NEWSZ_SSVC /\ rblock_range q SZ_SPCI_IMPL
    /\ as_RHEAP H s' ((p2, q, SZ_SPCI_IMPL) :: (p1, v, NEWSZ_SSVC) :: LB) m'
    /\ rw_cells bsegs m' v (SvcHdrCells (ssvc_hdr0 own) ++ [C8 (wz (q + O_SPC_STORAGE)); C8 (wz q)] ++ CookieCells j7)
    /\ addressable m' v NEWSZ_SSVC
    /\ AImplBlock ((p2, q, SZ_SPCI_IMPL) :: (p1, v, NEWSZ_SSVC) :: LB) m' q (mkIMPL (mkSPC AVP_SPCI_IMPL 1 1 1) 0 0 [] 0)
    /\ AAllocImpl ((p2, q, SZ_SPCI_IMPL) :: (p1, v, NEWSZ_SSVC) :: LB) m' allocb
    /\ AXStatics2 m'
    /\ Forall (fs_scratch H LF) XS
    /\ xpres H LB (bv_unsigned sp) XS m m'
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
    /\ as_AL H s' >= as_AL H s - create_ssvc_cost.

Definition create_ssvc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (ctx own allocb lo B shi : Z) (errv : word),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_CREATE_SSVC) fc None m (seg_rom bsegs) ->
    a0 = Z_to_bv 64 ctx -> a1 = Z_to_bv 64 own ->
    ro_cells bsegs m ctx [C8 (wz allocb)] -> 0 < ctx -> ctx mod 8 = 0 -> ctx + 8 <= aceil -> accessible m ctx 8 ->
    0 <= own < 2^64 ->
    0 < own -> own mod 8 = 0 ->     (* [comment removed for export] *)
    AAllocImpl LB m allocb -> AXStatics2 m ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    lb_bytes LB + NEWSZ_SSVC + SZ_SPCI_IMPL <= as_LIVE_MAX H -> Z.of_nat (length LB) + 2 <= as_LIVE_CNT_MAX H ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk bsegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ACREATE_SSVC_STACK ->
    rw_cells bsegs m (errno_addr tp) [C4 errv] -> mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
    bv_unsigned ra mod 2 = 0 ->
    (* [comment removed for export] *)
    bv_unsigned sp mod 16 = 0 ->
    as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat -> ACONST m ->
    stack0 m lo shi -> bv_unsigned sp + 64 <= shi ->
    create_ssvc_cost <= as_AL H s ->
    as_SR H (create_ssvc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF own allocb lo B shi m mo)
      (mkCfg msF mo).

End W2.
End HCW2.
