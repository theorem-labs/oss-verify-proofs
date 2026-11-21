(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Arr Bytes ZBridge Tac.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg RtCells ABase AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AArr.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U1B Require Import U2BObj U2BIface InfBBase.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition CLDONE_MS (cx : ictx) (ly : ilay) (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (st : ist)
    (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x26 x28 x29 x30 x31 : word) (m : amem) : machine_state :=
  (MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly)) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (l_Zs ly)) x19 x26 (Z_to_bv 64 2147450880) x22 (Z_to_bv 64 (t_hold st))
             (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x23 (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 (l_F0 ly)) x28 x29 x30 x31)
        FR (Z_to_bv 64 0x8fb2c) fc None m (seg_rom bsegs)).

Section K.
Variables (cx : ictx) (ly : ilay).
Variable AI : AMallocIface.
Variables (L : alayout) (RNG : footprint) (stA : astate) (LB : list ablock).
Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (POST : machine_state -> Prop).
Variables (LBc : list ablock) (m0 : amem) (payload : list Z) (fw : Z -> Z) (saved fk fksh : list cell).

Definition cldone_stmtA : Prop :=
  forall (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
         (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x26 x28 x29 x30 x31 : word) (m : amem),
    inf_ctx cx ly AI RNG LB ->
    Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = CODELENS -> t_nlen st + t_ndist st <= t_shave st -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    inf_vis cx ly st lf cf wf fo payload v0
            (Z_to_bv 64 (Z.shiftr (c_p cx + 152) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (c_p cx + 148) 3 + 2147450880)) v8 (Z_to_bv 64 (t_nlen st))
            (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m ->
    KALL cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (meas cx st) ->
    evtF bsegs RNG POST (CLDONE_MS cx ly gp tp FR fc st x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x26 x28 x29 x30 x31 m).
End K.
End CANSEC1.
