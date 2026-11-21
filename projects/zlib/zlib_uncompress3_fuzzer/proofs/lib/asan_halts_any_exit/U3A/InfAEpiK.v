(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AArr.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U3A Require Import U2AObj U2AIface InfABase.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Common Require Import DrvAgree RunDraw.
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
           (v0 v8 v16 v240 v504 vnext j512 j520 zti zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total back was pad : word)
           (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y26 y27 y28 y29 y30 y31 : word) (m1 : amem),
      sinv cx st lf cf -> inf_arr_ok cx wf fo -> 0 < rv < 18446744073709551616 ->
      inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v240 v504 vnext j512 j520
              (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (c_n cx - t_cin st)) zti (Z_to_bv 64 (c_ob cx + t_cout st)) (Z_to_bv 64 (c_osz cx - t_cout st))
              zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 (t_bits st)) back was pad m1 ->
      inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m1 ->
      evtF asegs RNG POST
        (MS (mkR y1 (Z_to_bv 64 (l_SPA ly)) gp tp y5 y6 y7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly)) (Z_to_bv 64 (l_F0 ly))
                 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 (Z_to_bv 64 rv)
                 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly)) y26 y27 y28 y29 y30 y31)
            FR (Z_to_bv 64 L_EPI) fc None m1 (seg_rom asegs)).
End K.
End CANSEC1.
