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
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.U1B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit AdlUBIface.
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

  (* W03 UNPATCHED: the state after the stores back of the leave join (strm next_out / avail_out /
     next_in / avail_in, state hold / bits), at 0x935c0: the shadow check of the wsize pointer, the first instruction
     of the window decision (inf_leave_dt). The totals come AFTER the window step in the unpatched order, so they are
     still the caller's here (the binders zti' / zto' / total' keep the patched shape; inf_leave_rs passes the old
     values). The register file read off the stores block: a3 = the wsize pointer (state + 72), a5 = the mode pointer
     (state + 8, read by the no-window test), s5 = the shadow of state->bits (reloaded in the stores), s2 = strm,
     s6 = the shadow base, s9 / s10 / s11 = the fake frame shadow / the fake frame / the return code, ra = the fake
     frame. *)
  Definition LV_RS (cx : ictx) (ly : ilay) (st : ist) (rv : Z) (lf cf wf fo : Z -> Z)
      (v0 v8 v16 v24 v240 v328 v512 j544 j552 zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check back was pad : word) : Prop :=
    forall (zti' zto' total' : word) (y5 y6 y7 y10 y11 y12 y14 y16 y17 y19 y20 y23 y24 y28 y29 y30 y31 : word) (m1 : amem),
      inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v24 v240 v328 v512 j544 j552
              (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (c_n cx - t_cin st)) zti' (Z_to_bv 64 (c_ob cx + t_cout st)) (Z_to_bv 64 (c_osz cx - t_cout st))
              zto' zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total' (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 (t_bits st)) back was pad m1 ->
      inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m1 ->
      evtF bsegs RNG POST
        (MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp y5 y6 y7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
                 y10 y11 y12 (Z_to_bv 64 (c_p cx + 72)) y14 (Z_to_bv 64 (c_p cx + 8)) y16 y17
                 (Z_to_bv 64 (l_Zs ly)) y19 y20 (Z_to_bv 64 (Z.shiftr (c_p cx + 104) 3 + 2147450880)) (Z_to_bv 64 2147450880) y23 y24
                 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 rv) y28 y29 y30 y31)
               FR (Z_to_bv 64 0x935c0) fc None m1 (seg_rom bsegs)).

  Lemma inf_leave_rs : forall (cx : ictx) (ly : ilay) (st : ist) (rv : Z) (lf cf wf fo : Z -> Z)
      (v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x6 x7 x10 x11 x12 x13 x14 x16 x19 x21 x23 x26 x28 x29 x30 x31 : word) (m : amem),
    inf_ctx cx ly AI RNG LB -> Z.of_nat (length payload) = c_n cx ->
    sinv cx st lf cf -> inf_arr_ok cx wf fo -> 0 <= rv < 18446744073709551616 ->
    inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m ->
    LV_RS cx ly st rv lf cf wf fo v0 v8 v16 v24 v240 v328 v512 j544 j552 zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check back was pad ->
    evtF bsegs RNG POST (LEAVE_MS ly gp tp FR fc L_LEAVE st (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 rv) x6 x7 x10 x11 x12 x13 x14 (Z_to_bv 64 (c_p cx + 8)) x16 x19 x21 x23 x26 x28 x29 x30 x31 m).
  Proof.
    intros until m. intros CTX PLEN SI ARR RRV VIS HID KRS.
    unfold LEAVE_MS, L_LEAVE. unfold LV_RS in KRS.
    inf_arm_open.
    Time zrung [0x935c0].
    eapply KRS; [inf_vis_close| inf_hid_close].
  Qed.
End S.
End CANSEC1.
