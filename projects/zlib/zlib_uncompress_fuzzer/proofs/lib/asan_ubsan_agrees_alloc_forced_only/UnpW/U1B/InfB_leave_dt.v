(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.U1B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import U2BKit U2BKit_p04. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.U1B Require Import InfBTraps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
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

  (* W03 UNPATCHED (the W02 model, a worker's InfA_leave_dt): in the unpatched order the window
     step comes right after the stores back, BEFORE the totals, the check and data_type (they are InfB_fin's
     inf_post). So: LV_K1 = the join after the window step (0x9365c, the totals), reached when updatewindow is not
     called; LV_K2 = the call of updatewindow (return point 0x935f4, inf_uwret); inf_leave_dt = the window decision,
     from the state after the stores (LV_RS's state, 0x935c0). The binder zdt' keeps the patched shape (data_type is
     not written on this path). *)
  (* the join after the window step: ra = the fake frame, s2 = strm, s5 = the shadow of state->bits, s6 = the shadow
     base, s9 / s10 / s11 = the fake frame shadow / the fake frame / the return code (InfB_fin's inf_fin) *)
  Definition LV_K1 (cx : ictx) (ly : ilay) (st : ist) (rv : Z) (lf cf wf fo : Z -> Z)
      (v0 v8 v16 v24 v240 v328 v512 j544 j552 zti zto zmsg zopq zadl zres zp1 zp2 zp3 havedict dmax check total back was pad : word) : Prop :=
    forall (zdt' : word) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y23 y24 y28 y29 y30 y31 : word) (m1 : amem),
      VISR cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 v512 j544 j552 zti zto zmsg zopq zdt' zadl zres zp1 zp2 zp3 havedict dmax check total back was pad m1 ->
      inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m1 ->
      evtF bsegs RNG POST
        (MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp y5 y6 y7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
                 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (l_Zs ly)) y19 y20
                 (Z_to_bv 64 (Z.shiftr (c_p cx + 104) 3 + 2147450880)) (Z_to_bv 64 2147450880) y23 y24
                 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 rv) y28 y29 y30 y31)
            FR (Z_to_bv 64 0x9365c) fc None m1 (seg_rom bsegs)).
  (* the call of updatewindow (return point 0x935f4): a0 = strm, a1 = next_out (put), a2 = out - left; the
     callee-saved registers the code after the return reads: s0, s1, s2, s5, s6, s9, s10, s11 *)
  Definition LV_K2 (cx : ictx) (ly : ilay) (st : ist) (rv : Z) (lf cf wf fo : Z -> Z)
      (v0 v8 v16 v24 v240 v328 v512 j544 j552 zti zto zmsg zopq zadl zres zp1 zp2 zp3 havedict dmax check total back was pad : word) : Prop :=
    forall (zdt' : word) (y5 y6 y7 y13 y14 y15 y16 y17 y19 y20 y23 y24 y28 y29 y30 y31 : word) (m1 : amem),
      VISR cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 v512 j544 j552 zti zto zmsg zopq zdt' zadl zres zp1 zp2 zp3 havedict dmax check total back was pad m1 ->
      inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m1 ->
      (c_w cx <> 0 \/ (t_out st <> c_osz cx - t_cout st /\ t_mode st <= 16208)) ->
      evtF bsegs RNG POST
        (MS (mkR (Z_to_bv 64 0x935f4) (Z_to_bv 64 (l_SPA ly)) gp tp y5 y6 y7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly)) (Z_to_bv 64 (l_Zs ly))
                 (Z_to_bv 64 (c_ob cx + t_cout st)) (Z_to_bv 64 (t_out st - (c_osz cx - t_cout st))) y13 y14 y15 y16 y17 (Z_to_bv 64 (l_Zs ly))
                 y19 y20 (Z_to_bv 64 (Z.shiftr (c_p cx + 104) 3 + 2147450880)) (Z_to_bv 64 2147450880) y23 y24
                 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 rv) y28 y29 y30 y31)
            FR (Z_to_bv 64 A_UPDATEWINDOW) fc None m1 (seg_rom bsegs)).

  (* the window decision, from the state after the stores back (0x935c0: the shadow check of the wsize pointer) *)
  Lemma inf_leave_dt : forall (cx : ictx) (ly : ilay) (st : ist) (rv : Z) (lf cf wf fo : Z -> Z)
      (v0 v8 v16 v24 v240 v328 v512 j544 j552 zti zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total back was pad : word)
      (x5 x6 x7 x10 x11 x12 x14 x16 x17 x19 x20 x23 x24 x28 x29 x30 x31 : word) (m : amem),
    inf_ctx cx ly AI RNG LB -> Z.of_nat (length payload) = c_n cx ->
    sinv cx st lf cf -> inf_arr_ok cx wf fo -> 0 <= rv < 18446744073709551616 ->
    VISR cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 v512 j544 j552 zti zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total back was pad m ->
    inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m ->
    LV_K1 cx ly st rv lf cf wf fo v0 v8 v16 v24 v240 v328 v512 j544 j552 zti zto zmsg zopq zadl zres zp1 zp2 zp3 havedict dmax check total back was pad ->
    LV_K2 cx ly st rv lf cf wf fo v0 v8 v16 v24 v240 v328 v512 j544 j552 zti zto zmsg zopq zadl zres zp1 zp2 zp3 havedict dmax check total back was pad ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
               x10 x11 x12 (Z_to_bv 64 (c_p cx + 72)) x14 (Z_to_bv 64 (c_p cx + 8)) x16 x17
               (Z_to_bv 64 (l_Zs ly)) x19 x20 (Z_to_bv 64 (Z.shiftr (c_p cx + 104) 3 + 2147450880)) (Z_to_bv 64 2147450880) x23 x24
               (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 rv) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x935c0) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros CTX PLEN SI ARR RRV VIS HID K1 K2.
    pose proof SI as (_ & _ & _ & MO). pose proof (proj1 MO) as REACH. clear MO.
    unfold LV_K1 in K1. unfold LV_K2 in K2.
    inf_arm_open.
    assert (MODER : 16180 <= mode <= 16210) by (unfold reach in REACH; cbv [HEAD DICTID MEM] in REACH; lia).
    destruct (Z.eqb_spec Wd 0) as [WZ|WNZ].
    - (* no window yet: out == left goes to the join; else a mode at BAD or above goes to the join; else (flush is 0) the call *)
      subst Wd. change (wsz (ICX u S D n 6341120 osz 0 cin0 cout0 W0 K0 zc)) with 0 in *.
      Time zrung [0x9365c; 0x94600].
      zbr KOUT.
      + zrung [0x9365c; 0x94600].
        eapply K1; [inf_vis_close| inf_hid_close].
      + zrung [0x9365c; 0x94600].
        zbr KMODE.
        * zrung [0x9365c; 0x94600].
          eapply K1; [inf_vis_close| inf_hid_close].
        * zrung [0x9365c; 0x94600].
          eapply K2; [inf_vis_close| inf_hid_close| right; split; lia].
    - (* a window: the call *)
      assert (WSZ : wsz (ICX u S D n 6341120 osz Wd cin0 cout0 W0 K0 zc) = 32768)
        by (unfold wsz; cbn [c_w]; destruct (Z.eqb_spec Wd 0); [contradiction| reflexivity]).
      rewrite WSZ in *.
      Time zrung [0x9365c; 0x94600].
      lazymatch goal with H : rw_cells bsegs _ S (C8 _ :: _) |- _ => rewrite <- WSZ in H end.
      eapply K2; [inf_vis_close| inf_hid_close| left; exact WNZ].
    Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End S.
End CANSEC1.
