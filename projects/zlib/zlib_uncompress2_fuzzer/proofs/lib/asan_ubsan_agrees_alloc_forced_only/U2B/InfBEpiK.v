(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AArr U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2B Require Import U2BObj U2BIface InfBBase.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import DrvAgree RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section K.
  Variable AI : AMallocIface.
  Variables (L : alayout) (RNG : footprint) (stA : astate) (LB : list ablock).
  Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (POST : machine_state -> Prop).
  Variables (LBc : list ablock) (m0 : amem) (payload : list Z) (fw : Z -> Z) (saved fk fksh : list cell).

  Definition LV_KEPI (cx : ictx) (ly : ilay) : Prop :=
    forall (st : ist) (rv : Z) (lf cf wf fo : Z -> Z)
           (v0 v8 v16 v24 v240 v328 v512 j544 j552 zti zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total back was pad : word)
           (y2 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y25 y28 y29 y30 y31 : word) (m1 : amem),
      sinv cx st lf cf -> inf_arr_ok cx wf fo -> 0 < rv < 18446744073709551616 ->
      inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v24 v240 v328 v512 j544 j552
              (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (c_n cx - t_cin st)) zti (Z_to_bv 64 (c_ob cx + t_cout st)) (Z_to_bv 64 (c_osz cx - t_cout st))
              zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 (t_bits st)) back was pad m1 ->
      inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m1 ->
      evtF bsegs RNG POST
        (MS (mkR (Z_to_bv 64 (l_F0 ly)) y2 gp tp y5 y6 y7 (Z_to_bv 64 (l_SP ly)) y9 y10
                 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23
                 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) y25 (Z_to_bv 64 rv) (Z_to_bv 64 (l_F0 ly)) y28 y29 y30 y31)
            FR (Z_to_bv 64 L_EPI) fc None m1 (seg_rom bsegs)).
End K.
End CANSEC1.
