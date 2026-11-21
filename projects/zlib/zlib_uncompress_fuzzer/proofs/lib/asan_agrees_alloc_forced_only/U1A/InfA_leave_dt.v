(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U1A Require Import U2AObj U2AClient U2AIface InfABase InfAKit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.
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

  Notation VISR cx ly st lf cf wf fo v0 v8 v16 v240 v504 vnext j512 j520 zti zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total back was pad m :=
    (inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v240 v504 vnext j512 j520
            (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (c_n cx - t_cin st)) zti (Z_to_bv 64 (c_ob cx + t_cout st)) (Z_to_bv 64 (c_osz cx - t_cout st))
            zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 (t_bits st)) back was pad m).

  Definition LV_K1 (cx : ictx) (ly : ilay) (st : ist) (rv : Z) (lf cf wf fo : Z -> Z)
      (v0 v8 v16 v240 v504 vnext j512 j520 zti zto zmsg zopq zadl zres zp1 zp2 zp3 havedict dmax check total back was pad : word) : Prop :=
    forall (zdt' : word) (y1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y26 y28 y30 y31 : word) (m1 : amem),
      VISR cx ly st lf cf wf fo v0 v8 v16 v240 v504 vnext j512 j520 zti zto zmsg zopq zdt' zadl zres zp1 zp2 zp3 havedict dmax check total back was pad m1 ->
      inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m1 ->
      evtF asegs RNG POST
        (* InfA_fin's inf_fin entry at 1.4 (out a1, rv s7, F0 shadow s8, F0 s9, have s11, left t4) *)
        (MS (mkR y1 (Z_to_bv 64 (l_SPA ly)) gp tp y5 y6 y7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly)) (Z_to_bv 64 (l_F0 ly))
                 (Z_to_bv 64 (t_out st)) y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 (Z_to_bv 64 rv)
                 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly)) y26 (Z_to_bv 64 (c_n cx - t_cin st)) y28
                 (Z_to_bv 64 (c_osz cx - t_cout st)) y30 y31)
            FR (Z_to_bv 64 0x92964) fc None m1 (seg_rom asegs)).
  Definition LV_K2 (cx : ictx) (ly : ilay) (st : ist) (rv : Z) (lf cf wf fo : Z -> Z)
      (v0 v8 v16 v240 v504 vnext j512 j520 zti zto zmsg zopq zadl zres zp1 zp2 zp3 havedict dmax check total back was pad : word) : Prop :=
    forall (zdt' : word) (y5 y6 y7 y13 y14 y15 y16 y17 y22 y26 y28 y31 : word) (m1 : amem),
      VISR cx ly st lf cf wf fo v0 v8 v16 v240 v504 vnext j512 j520 zti zto zmsg zopq zdt' zadl zres zp1 zp2 zp3 havedict dmax check total back was pad m1 ->
      inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m1 ->
      (c_w cx <> 0 \/ (t_out st <> c_osz cx - t_cout st /\ t_mode st <= 16208)) ->
      evtF asegs RNG POST
        (* the 1.4 call state at A_UPDATEWINDOW (0x928ac jal), read off probe PgLeaveB1: left saved in s3,
           copy in s4, SHB s5, rv s7, F0 shadow s8, F0 s9, have s11, left t4, mode shadow t5 *)
        (MS (mkR (Z_to_bv 64 0x92900) (Z_to_bv 64 (l_SPA ly)) gp tp y5 y6 y7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly)) (Z_to_bv 64 (l_Zs ly))
                 (Z_to_bv 64 (c_ob cx + t_cout st)) (Z_to_bv 64 (t_out st - (c_osz cx - t_cout st))) y13 y14 y15 y16 y17 (Z_to_bv 64 (l_Zs ly))
                 (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (t_out st - (c_osz cx - t_cout st))) (Z_to_bv 64 2147450880) y22 (Z_to_bv 64 rv)
                 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly)) y26 (Z_to_bv 64 (c_n cx - t_cin st)) y28
                 (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880)) y31)
            FR (Z_to_bv 64 A_UPDATEWINDOW) fc None m1 (seg_rom asegs)).

  Lemma inf_leave_dt : forall (cx : ictx) (ly : ilay) (st : ist) (rv : Z) (lf cf wf fo : Z -> Z)
      (v0 v8 v16 v240 v504 vnext j512 j520 zti zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total back was pad : word)
      (x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x22 x26 x28 x31 : word) (m : amem),
    inf_ctx cx ly AI RNG LB -> Z.of_nat (length payload) = c_n cx ->
    sinv cx st lf cf -> inf_arr_ok cx wf fo -> 0 <= rv < 18446744073709551616 ->
    VISR cx ly st lf cf wf fo v0 v8 v16 v240 v504 vnext j512 j520 zti zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total back was pad m ->
    inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m ->
    LV_K1 cx ly st rv lf cf wf fo v0 v8 v16 v240 v504 vnext j512 j520 zti zto zmsg zopq zadl zres zp1 zp2 zp3 havedict dmax check total back was pad ->
    LV_K2 cx ly st rv lf cf wf fo v0 v8 v16 v240 v504 vnext j512 j520 zti zto zmsg zopq zadl zres zp1 zp2 zp3 havedict dmax check total back was pad ->
    evtF asegs RNG POST
      (* the 1.4 state at 0x927dc, read off probe PgLeaveA1 (inf_leave_main's walk from LEAVE_MS):
         a1 = the bits shadow, s4 = out - left, s5 = SHB, s7 = rv, s8 / s9 = the fake frame, s11 = have, t4 = left *)
      (MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly)) (Z_to_bv 64 (l_F0 ly))
               (Z_to_bv 64 (Z.shiftr (c_p cx + 104) 3 + 2147450880)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (l_Zs ly)) x19
               (Z_to_bv 64 (t_out st - (c_osz cx - t_cout st))) (Z_to_bv 64 2147450880) x22 (Z_to_bv 64 rv)
               (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly)) x26 (Z_to_bv 64 (c_n cx - t_cin st))
               x28 (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880)) x31)
          FR (Z_to_bv 64 0x9282c) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros CTX PLEN SI ARR RRV VIS HID K1 K2.
    pose proof SI as (_ & _ & _ & MO). pose proof (proj1 MO) as REACH. clear MO.
    unfold LV_K1 in K1. unfold LV_K2 in K2.
    inf_arm_open.
    assert (MODER : 16180 <= mode <= 16210) by (unfold reach in REACH; cbv [HEAD DICTID MEM] in REACH; lia).
    destruct (Z.eqb_spec Wd 0) as [WZ|WNZ].
    -
      subst Wd. change (wsz (ICX u S D n 6335680 osz 0 cin0 cout0 W0 K0 zc)) with 0 in *.
      Time zrunb [0x92964; 0x93678].
      zbr KOUT.
      +
        zrunb [0x92964; 0x93678]. (* [U14] 1.4 joins at 0x92910 ld a1,432(s1) *)
        eapply (K1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [inf_vis_close| inf_hid_close].
      + zrunb [0x92964; 0x93678].
        zbr KMODE.
        *
          zrunb [0x92964; 0x93678]. (* [U14] 1.4 joins at 0x92910 ld a1,432(s1) *)
        eapply (K1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [inf_vis_close| inf_hid_close].
        * zrunb [0x92964; 0x93678].
          eapply (K2 _ _ _ _ _ _ _ _ _ _ _ _ _); [inf_vis_close| inf_hid_close| right; split; lia].
    -
      assert (WSZ : wsz (ICX u S D n 6335680 osz Wd cin0 cout0 W0 K0 zc) = 32768)
        by (unfold wsz; cbn [c_w]; destruct (Z.eqb_spec Wd 0); [contradiction| reflexivity]).
      rewrite WSZ in *.
      Time zrunb [0x92964; 0x93678].
      lazymatch goal with H : rw_cells asegs _ S (C8 _ :: _) |- _ => rewrite <- WSZ in H end.
      eapply (K2 _ _ _ _ _ _ _ _ _ _ _ _ _); [inf_vis_close| inf_hid_close| left; exact WNZ].
    (* v240 is a vestige binder at 1.4 *)
    Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End S.
End CANSEC1.
