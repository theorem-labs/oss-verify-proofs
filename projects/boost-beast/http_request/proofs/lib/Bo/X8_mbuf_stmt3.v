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
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AXPRep AXRep_fields AXRep_mbuf.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import N8Kit N8Kit2 N8Kit3 X8Kit X8SRKit X8_mbuf_stmt.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem RBShape RBTac RBSafe DList.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

(* [comment removed for export] *)
Definition ocb_stmtB : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (P rem b : Z) (es : list mbe) (insz n src E lo B shi : Z)
         (bs ej : list byte) (errv : word) (r344 : list cell),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_ON_CHUNK_BODY_IMPL) fc None m (seg_rom bsegs) ->
    a0 = wz P -> a1 = wz rem -> a2 = wz src -> a3 = wz n -> a4 = wz E -> 0 <= rem < 2^64 ->
    0 <= P ->
    rw_cells bsegs m (P + 336) (C8 (wz 0) :: r344) -> (P + 336) mod 8 = 0 -> accessible m (P + 336) 8 ->
    (P + 336 + Z.of_nat (cells_size (C8 (wz 0) :: r344)) <= lo \/ bv_unsigned sp <= P + 336) ->
    aobj LB LF (P + 336) 8 ->                            (* [comment removed for export] *)
    lo <= bv_unsigned sp - OCB_STACK ->                  (* [comment removed for export] *)
    (length LF + 4 < AFS_MAXLIVE)%nat ->                 (* [comment removed for export] *)
    put_pre H
      (as_SR H (put_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF b es insz n src E lo B shi bs m mo)
         (mkCfg msF mo))
      sp ra tp msF m mo s LB LF (P + 232) b es insz n src E lo B shi bs ej errv.

End HCW.
