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
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.U1B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit AdlUBIface InfB_leave_dt InfB_leave_adl InfB_leave_rs.
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
  Hypothesis ADL : adler32_stmtU.

  Lemma inf_leave_main : forall (cx : ictx) (ly : ilay) (st : ist) (rv : Z) (lf cf wf fo : Z -> Z)
      (v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x6 x7 x10 x11 x12 x13 x14 x16 x19 x21 x23 x26 x28 x29 x30 x31 : word) (m : amem),
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
    evtF bsegs RNG POST (LEAVE_MS ly gp tp FR fc L_LEAVE st (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 rv) x6 x7 x10 x11 x12 x13 x14 (Z_to_bv 64 (c_p cx + 8)) x16 x19 x21 x23 x26 x28 x29 x30 x31 m).
  (* W03 UNPATCHED: the leave join is the stores back (inf_leave_rs) and then the window decision
     (inf_leave_dt). The totals, the check and data_type come after the window step (InfB_fin's inf_fin / inf_post).
     K1 / K2 keep the patched form (quantified over the totals and the check), so their users need no change of
     shape. Proof using All keeps ADL among the arguments, as before (the check is no longer walked here). *)
  Proof using All.
    intros until m. intros CTX PLEN SI ARR RRV VIS HID K1 K2.
    eapply (inf_leave_rs AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly st rv lf cf wf fo); try eassumption.
    clear VIS HID m. unfold LV_RS. intros zti1 zto1 total1 y5 y6 y7 y10 y11 y12 y14 y16 y17 y19 y20 y23 y24 y28 y29 y30 y31 m VIS HID.
    eapply (inf_leave_dt AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly st rv lf cf wf fo);
      [exact CTX| exact PLEN| exact SI| exact ARR| exact RRV| exact VIS| exact HID| eapply K1| eapply K2].
  Qed.
End S.
End CANSEC1.
