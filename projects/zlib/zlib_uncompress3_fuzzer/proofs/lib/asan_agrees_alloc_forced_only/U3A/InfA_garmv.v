(* garmV, the arm statement for the 1.4 fall-through
   chain LENEXT / DIST / DISTEXT / MATCH.  It is garm_stmtA (InfA_w7base) with frame slot 504 free: the codelens DONE path
   reaches LEN_ (0x90c7c) with slot 504 = shadow(S+148) (stored at 0x8f4fc), and no instruction from 0x90c7c to the jump back
   to DISP (0x91aa0) reads or rewrites slot 504.  t2 stays S+56 here (LEN reloads it at 0x91154); LEN_ and LEN use
   garmC (InfA_garmc), which frees t2 as well. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AImg RtCells ABase AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AArr.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U3A Require Import U2AObj U2AIface InfABase InfA_w7base.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section K.
Variables (cx : ictx) (ly : ilay).
Variable AI : AMallocIface.
Variables (L : alayout) (RNG : footprint) (stA : astate) (LB : list ablock).
Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (POST : machine_state -> Prop).
Variables (LBc : list ablock) (m0 : amem) (payload : list Z) (fw : Z -> Z) (saved fk fksh : list cell).

(* The slot-504 cell is named by the v240 binder (inf_vis ignores its own v240 argument), so a chain walk restated from
   garm_stmtA only swaps two VIS arguments. *)
Definition garmv_stmtA (Lb X : Z) : Prop :=
  forall (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word) (x5 x6 x11 x12 x13 x14 x15 x16 x17 x22 x23 : word) (m : amem),
    inf_ctx cx ly AI RNG LB ->
    Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = X -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    inf_vis cx ly st lf cf wf fo payload v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m ->
    KALL cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (meas cx st) ->
    evtF asegs RNG POST (GARM_MS cx ly gp tp FR fc Lb st x5 x6 x11 x12 x13 x14 x15 x16 x17 x22 x23 m).

Lemma garmv_garm : forall Lb X, garmv_stmtA Lb X -> garm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X.
Proof.
  intros Lb X H. unfold garm_stmtA. intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA.
  exact (H st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad
           x5 x6 x11 x12 x13 x14 x15 x16 x17 x22 x23 m CTX PAYR PLEN MODE SI ARR VIS HID KA).
Qed.
End K.
End CANSEC1.
