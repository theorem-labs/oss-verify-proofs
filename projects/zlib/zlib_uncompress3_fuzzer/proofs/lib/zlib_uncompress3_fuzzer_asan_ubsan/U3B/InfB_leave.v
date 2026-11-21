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
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U3B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit AdlUBIface InfB_leave_dt InfB_leave_adl InfB_leave_rs.
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
  Hypothesis ADL : adler32_stmtU.

  Lemma inf_leave_main : forall (cx : ictx) (ly : ilay) (st : ist) (rv : Z) (lf cf wf fo : Z -> Z)
      (v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x6 x7 x10 x11 x12 x13 x14 x15 x16 x19 x21 x23 x26 x28 x29 x30 x31 : word) (m : amem),
    inf_ctx cx ly AI RNG LB -> Z.of_nat (length payload) = c_n cx ->
    sinv cx st lf cf -> inf_arr_ok cx wf fo -> 0 <= rv < 18446744073709551616 ->
    inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m ->
    (forall zti' zto' zadl' check' total' : word,
       LV_K1 AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly st rv lf cf wf fo
             v0 v8 v16 v24 v240 v328 v512 j544 j552 zti' zto' zmsg zopq zadl' zres zp1 zp2 zp3 havedict dmax check' total' back was pad) ->
    (forall zti' zto' zadl' check' total' : word,
       LV_K2 AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly st rv lf cf wf fo
             v0 v8 v16 v24 v240 v328 v512 j544 j552 zti' zto' zmsg zopq zadl' zres zp1 zp2 zp3 havedict dmax check' total' back was pad) ->
    evtF bsegs RNG POST (LEAVE_MS ly gp tp FR fc L_LEAVE st (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 rv) x6 x7 x10 x11 x12 x13 x14 x15 x16 x19 x21 x23 x26 x28 x29 x30 x31 m).
  Proof.
    intros until m. intros CTX PLEN SI ARR RRV VIS HID K1 K2.
    eapply (inf_leave_rs AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly st rv lf cf wf fo); try eassumption.
    clear VIS HID m. unfold LV_RS. intros zti1 zto1 total1 y6 y7 y10 y12 y16 y19 y23 y26 y28 y29 y30 y31 m VIS HID.
    pose proof HID as (AH0 & _). pose proof (AI_rtcells AI _ _ _ _ _ AH0) as ART. unfold artcells in ART.
    destruct ART as (_ & RTG & _ & _ & RTS & _).
    inf_arm_open.
    lazymatch goal with H : rw_cells bsegs _ S (C8 _ :: _) |- _ => rename H into SSC' end.
    rw_split SSC' 3%nat SSA SSB. rw_split SSB 1%nat SW SSD.
    eapply (rw_cells_recast bsegs _ _ _ [C1 (Z_to_bv 8 5); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) in SW; [| cbn; tauto| reflexivity| reflexivity].
    zs.
    eapply (rw_cells_recast bsegs _ _ _ [C4 (Z_to_bv 64 5)]) in SW; [| cbn; tauto| reflexivity| reflexivity].
    rw_join SW SSD SSB'. rw_join SSA SSB' SSC'.
    Time zrung [0x9389c].
    zs.
    zbr KOUT.
    -
      eapply (inf_leave_dt AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh
                (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
                (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) rv lf cf wf fo);
        [exact CTX0| exact PLEN| exact SI| exact ARR| exact RRV| inf_vis_close| inf_hid_close| eapply K1| eapply K2].
    -
      eapply (inf_leave_adl AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh ADL
                (ICX u S D n 6341952 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
                (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) rv lf cf wf fo);
        [exact CTX0| exact PLEN| exact SI| exact ARR| exact RRV| exact KOUT| inf_vis_close| inf_hid_close| intros; eapply K1| intros; eapply K2].
  Qed.
End S.
End CANSEC1.
