(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Lib Require Import Arr Bytes ZBridge Tac.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.BothW Require Import BImg RtCells ABase AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U2A Require Import U2AArr.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U3B Require Import U2BObj U2BIface InfBBase.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition GARM_MS (cx : ictx) (ly : ilay) (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (pc : Z) (st : ist)
    (x6 x7 x10 x11 x12 x13 x14 x16 x19 x20 x22 x25 x26 x28 x29 x30 x31 : word) (m : amem) : machine_state :=
  (MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (t_bits st)) x6 x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly)) x10 x11 x12 x13 x14
             (Z_to_bv 64 (c_p cx + 8)) x16 (Z_to_bv 64 (c_n cx - t_cin st))
             (Z_to_bv 64 (l_Zs ly)) x19 x20 (Z_to_bv 64 2147450880) x22 (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x25 x26
             (Z_to_bv 64 (l_F0 ly)) x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None m (seg_rom bsegs)).

Section K.
Variables (cx : ictx) (ly : ilay).
Variable AI : AMallocIface.
Variables (L : alayout) (RNG : footprint) (stA : astate) (LB : list ablock).
Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (POST : machine_state -> Prop).
Variables (LBc : list ablock) (m0 : amem) (payload : list Z) (fw : Z -> Z) (saved fk fksh : list cell).

Definition garm_stmtA (Lb X : Z) : Prop :=
  forall (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
         (x6 x7 x10 x11 x12 x13 x14 x16 x19 x20 x22 x25 x26 x28 x29 x30 x31 : word) (m : amem),
    inf_ctx cx ly AI RNG LB ->
    Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = X -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v24 v240 v328 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m ->
    KALL cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (meas cx st) ->
    evtF bsegs RNG POST (GARM_MS cx ly gp tp FR fc Lb st x6 x7 x10 x11 x12 x13 x14 x16 x19 x20 x22 x25 x26 x28 x29 x30 x31 m).

Lemma garm_arm : forall Lb X, garm_stmtA Lb X -> arm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X.
Proof.
  intros Lb X H. unfold arm_stmtA, ARM_MS. intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA.
  exact (H st lf cf wf fo v0 v8 v16 v24 v240 v328 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad
           x6 x7 x10 x11 x12 x13 x14 x16 x19 x20 x22 x25 _ x28 _ x30 x31 m CTX PAYR PLEN MODE SI ARR VIS HID KA).
Qed.
End K.
End CANSEC1.
