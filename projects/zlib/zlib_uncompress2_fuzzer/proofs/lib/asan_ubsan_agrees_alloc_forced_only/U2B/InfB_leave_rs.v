(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AObj U2AStore InfAGlue InfPure.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit AdlUBIface.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2B Require Import U2BKit U2BKit_p04 InfBTraps.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
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

  Definition LV_RS (cx : ictx) (ly : ilay) (st : ist) (rv : Z) (lf cf wf fo : Z -> Z)
      (v0 v8 v16 v24 v240 v328 v512 j544 j552 zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check back was pad : word) : Prop :=
    forall (zti' zto' total' : word) (y6 y7 y10 y12 y16 y19 y23 y26 y28 y29 y30 y31 : word) (m1 : amem),
      inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v24 v240 v328 v512 j544 j552
              (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (c_n cx - t_cin st)) zti' (Z_to_bv 64 (c_ob cx + t_cout st)) (Z_to_bv 64 (c_osz cx - t_cout st))
              zto' zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total' (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 (t_bits st)) back was pad m1 ->
      inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m1 ->
      evtF bsegs RNG POST
        (* [U14B] A2 2026-11-12: the 1.4 combined register file at 0x937d4, read off build c2's goal of inf_leave_rs
           (tools/regtree.py): a3 = &flags (S + 28), a4 = &wrap (S + 16), a5 = &total_out (Zs + 40) (1.3.1: a3 = S + 12,
           a4 = S + 28, a5 = S + 16); the dispatch homes at 1.4: s4 = out - avail_out, s5 = shadow base, s7 = hold,
           s8 = shadow(F0), s10 = the return value (1.3.1: s5, s9, s8, s4, s6). The binders keep their 1.3.1 names. *)
        (MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (t_bits st)) y6 y7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
                    y10 (Z_to_bv 64 ((t_out st - (c_osz cx - t_cout st)) mod 4294967296)) y12 (Z_to_bv 64 (c_p cx + 28)) (Z_to_bv 64 (c_p cx + 16)) (Z_to_bv 64 (l_Zs ly + 40)) y16
                    (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 (l_Zs ly)) y19 (Z_to_bv 64 (t_out st - (c_osz cx - t_cout st)))
                    (Z_to_bv 64 2147450880) y23 (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) y26 (Z_to_bv 64 rv)
                    (Z_to_bv 64 (l_F0 ly)) y28 y29 y30 y31)
               FR (Z_to_bv 64 0x9379c) fc None m1 (seg_rom bsegs)).

  Lemma inf_leave_rs : forall (cx : ictx) (ly : ilay) (st : ist) (rv : Z) (lf cf wf fo : Z -> Z)
      (v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x6 x7 x10 x11 x12 x13 x14 x15 x16 x19 x21 x23 x26 x28 x29 x30 x31 : word) (m : amem),
    inf_ctx cx ly AI RNG LB -> Z.of_nat (length payload) = c_n cx ->
    sinv cx st lf cf -> inf_arr_ok cx wf fo -> 0 <= rv < 18446744073709551616 ->
    inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m ->
    LV_RS cx ly st rv lf cf wf fo v0 v8 v16 v24 v240 v328 v512 j544 j552 zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check back was pad ->
    evtF bsegs RNG POST (LEAVE_MS ly gp tp FR fc L_LEAVE st (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 rv) x6 x7 x10 x11 x12 x13 x14 x15 x16 x19 x21 x23 x26 x28 x29 x30 x31 m).
  Proof.
    intros until m. intros CTX PLEN SI ARR RRV VIS HID KRS.
    unfold LEAVE_MS, L_LEAVE. unfold LV_RS in KRS.
    inf_arm_open.
    Time zrung [0x9379c].
    eapply (KRS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [inf_vis_close| inf_hid_close].
  Qed.
End S.
End CANSEC1.
