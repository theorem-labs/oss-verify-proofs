(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U3B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U3B Require Import U2BKit U2BKit_p04 InfBTraps.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.
Local Ltac ub_is_trap pc ::= ub_in_traps inf_traps pc.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= farr_store_extra m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= farr_call_extra segs W m m' MU WM.


Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variable AI : AMallocIface.
  Variables (L : alayout) (RNG : footprint) (stA : astate) (LB : list ablock).
  Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (POST : machine_state -> Prop).
  Variables (LBc : list ablock) (m0 : amem) (payload : list Z) (fw : Z -> Z) (saved fk fksh : list cell).

  Notation VISR cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 v512 j544 j552 zti zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total back was pad m :=
    (inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v24 v240 v328 v512 j544 j552
            (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (c_n cx - t_cin st)) zti (Z_to_bv 64 (c_ob cx + t_cout st)) (Z_to_bv 64 (c_osz cx - t_cout st))
            zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 (t_bits st)) back was pad m).

  Definition LV_K1 (cx : ictx) (ly : ilay) (st : ist) (rv : Z) (lf cf wf fo : Z -> Z)
      (v0 v8 v16 v24 v240 v328 v512 j544 j552 zti zto zmsg zopq zadl zres zp1 zp2 zp3 havedict dmax check total back was pad : word) : Prop :=
    forall (zdt' : word) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y21 y23 y24 y26 y28 y29 y30 y31 : word) (m1 : amem),
      VISR cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 v512 j544 j552 zti zto zmsg zopq zdt' zadl zres zp1 zp2 zp3 havedict dmax check total back was pad m1 ->
      inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m1 ->
      evtF bsegs RNG POST
        (MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp y5 y6 y7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
                 (* [U14B] A2 2026-11-12: the 1.4 homes at 0x93b24 (build c2's goal of inf_leave_dt, tools/regtree.py):
                    s5 = shadow base, s8 = shadow(F0), s10 = the return value (1.3.1: s9, s4, s6); s4 / s6 / s7 / s9 free *)
                 y10 y11 y12 y13 y14 y15 y16 (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 0)
                 y21 (Z_to_bv 64 2147450880) y23 y24 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) y26 (Z_to_bv 64 rv) (Z_to_bv 64 (l_F0 ly)) y28 y29 y30 y31)
            FR (Z_to_bv 64 0x93aec) fc None m1 (seg_rom bsegs)).
  Definition LV_K2 (cx : ictx) (ly : ilay) (st : ist) (rv : Z) (lf cf wf fo : Z -> Z)
      (v0 v8 v16 v24 v240 v328 v512 j544 j552 zti zto zmsg zopq zadl zres zp1 zp2 zp3 havedict dmax check total back was pad : word) : Prop :=
    (* [U14B] A2 2026-11-12: at 1.4 the updatewindow call site saves avail_in in s5 (0x93ab4 mv s5,a7; 1.3.1: 0x935e0
       mv s7,a7), so NO register holds the shadow base at the call: the 1.3.1 s9 = shadow base becomes the free binder
       y25. The 1.4 file at the call (0x93ac4 jal 0x94950): a2 = s4 = out - avail_out, s5 = avail_in, s8 = shadow(F0),
       s10 = the return value; s6 / s7 / s9 free. *)
    forall (zdt' : word) (y5 y6 y7 y13 y14 y15 y16 y17 y24 y25 y26 y28 y29 y30 y31 : word) (m1 : amem),
      VISR cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 v512 j544 j552 zti zto zmsg zopq zdt' zadl zres zp1 zp2 zp3 havedict dmax check total back was pad m1 ->
      inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m1 ->
      (c_w cx <> 0 \/ (t_out st <> c_osz cx - t_cout st /\ t_mode st <= 16208)) ->
      evtF bsegs RNG POST
        (MS (mkR (Z_to_bv 64 0x93a90) (Z_to_bv 64 (l_SPA ly)) gp tp y5 y6 y7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly)) (Z_to_bv 64 (l_Zs ly))
                 (Z_to_bv 64 (c_ob cx + t_cout st)) (Z_to_bv 64 (t_out st - (c_osz cx - t_cout st))) y13 y14 y15 y16 y17 (Z_to_bv 64 (l_Zs ly))
                 (Z_to_bv 64 0) (Z_to_bv 64 (t_out st - (c_osz cx - t_cout st))) (Z_to_bv 64 (c_n cx - t_cin st))
                 y24 y25 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) y26 (Z_to_bv 64 rv) (Z_to_bv 64 (l_F0 ly)) y28 y29 y30 y31)
            FR (Z_to_bv 64 A_UPDATEWINDOW) fc None m1 (seg_rom bsegs)).

  Lemma inf_leave_dt : forall (cx : ictx) (ly : ilay) (st : ist) (rv : Z) (lf cf wf fo : Z -> Z)
      (v0 v8 v16 v24 v240 v328 v512 j544 j552 zti zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total back was pad : word)
      (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x19 x23 x24 x26 x28 x29 x30 x31 : word) (m : amem),
    inf_ctx cx ly AI RNG LB -> Z.of_nat (length payload) = c_n cx ->
    sinv cx st lf cf -> inf_arr_ok cx wf fo -> 0 <= rv < 18446744073709551616 ->
    VISR cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 v512 j544 j552 zti zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total back was pad m ->
    inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m ->
    LV_K1 cx ly st rv lf cf wf fo v0 v8 v16 v24 v240 v328 v512 j544 j552 zti zto zmsg zopq zadl zres zp1 zp2 zp3 havedict dmax check total back was pad ->
    LV_K2 cx ly st rv lf cf wf fo v0 v8 v16 v24 v240 v328 v512 j544 j552 zti zto zmsg zopq zadl zres zp1 zp2 zp3 havedict dmax check total back was pad ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
               (* [U14B] A2 2026-11-12: a3 is free at 1.4 (0x939d0 ld a3,336(s1) reloads it; 1.3.1 kept S + 12 in a3) *)
               x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 (l_Zs ly)) x19
               (Z_to_bv 64 (t_out st - (c_osz cx - t_cout st))) (Z_to_bv 64 2147450880) x23 x24 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880))
               x26 (Z_to_bv 64 rv) (Z_to_bv 64 (l_F0 ly)) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x9398c) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros CTX PLEN SI ARR RRV VIS HID K1 K2.
    pose proof SI as (_ & _ & _ & MO). pose proof (proj1 MO) as REACH. clear MO.
    unfold LV_K1 in K1. unfold LV_K2 in K2.
    inf_arm_open.
    assert (MODER : 16180 <= mode <= 16210) by (unfold reach in REACH; cbv [HEAD DICTID MEM] in REACH; lia).
    Time zrung [0x93a64; 0x93aec; 0x94918].
    destruct (Z.eqb_spec Wd 0) as [WZ|WNZ].
    -
      subst Wd. change (wsz (ICX u S D n 6341952 osz 0 cin0 cout0 W0 K0 zc)) with 0 in *.
      Time zrung [0x93ac8; 0x93aec; 0x94918].
      zs.
      zbr KOUT.
      +
        eapply (K1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [inf_vis_close| inf_hid_close].
      + zrung [0x93ad4; 0x93aec; 0x94918].
        zs.
        zbr KMODE.
        *
          eapply (K1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [inf_vis_close| inf_hid_close].
        * zrung [0x93aec; 0x94918].
          eapply (K2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [inf_vis_close| inf_hid_close| right; split; lia].
    -
      assert (WSZ : wsz (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc) = 32768)
        by (unfold wsz; cbn [c_w]; destruct (Z.eqb_spec Wd 0); [contradiction| reflexivity]).
      rewrite WSZ in *.
      Time zrung [0x93aec; 0x94918].
      lazymatch goal with H : rw_cells bsegs _ S (C8 _ :: _) |- _ => rewrite <- WSZ in H end.
      eapply (K2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [inf_vis_close| inf_hid_close| left; exact WNZ].
  Qed.
End S.
End CANSEC1.
