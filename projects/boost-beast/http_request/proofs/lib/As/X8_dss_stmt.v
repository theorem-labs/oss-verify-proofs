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
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsIface AsIface5 AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2
     AsTRList X8Kit X8SRKit X8_asio_stmt_alloc X8_stream_stmt X8_stream_stmt3.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ADSS_STACK : Z := 16 + ADOBJ_SSVC_STACK.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  (* [comment removed for export] *)
  Definition destroy_alloc_ssvc_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB : list block) (LF : list fframe) (S ioc implb allocb vb lo B shi : Z) (errv : word) (Sv : svch),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 P_A_DESTROY_ALLOC_SSVC) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 S ->
      AStreamSvc LB m S Sv implb -> sv_owner Sv = ioc ->
      ro_cells asegs m ioc [C8 (wz allocb)] -> 0 < ioc -> ioc mod 8 = 0 -> ioc + 8 <= aceil -> accessible m ioc 8 ->
      AImplBlockC LB m implb (mkIMPL (mkSPC AVP_SPCI_IMPL 1 1 1) 0 vb [] 1) ->
      AAllocImpl LB m allocb -> AXStatics2 m ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ADSS_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned ra mod 2 = 0 ->
      (* [comment removed for export] *)
      bv_unsigned sp mod 16 = 0 ->
      as_RFS H LF m -> ACONST m -> stack0 m lo shi -> bv_unsigned sp <= shi ->
      dos_cost H <= as_AL H s ->
      as_SR H (dealloc_obj_ssvc_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF S implb allocb vb lo B shi errv m mo)
        (mkCfg msF mo).
End HCW.
