(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AShadow U2AKit U2AArr U2ABlob U2AStore InfAGlue InfPure InfPure_entry.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U1B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfBIface.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U1B Require Import U2BKit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import RunDraw.
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

  Definition F0_cells (jk : list byte) (flagp : word) : list cell :=
    [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 95921); C8 (Z_to_bv 64 581020); CB 32 jk; C8 flagp].
  Definition F0_shadow : list cell :=
    [C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
     C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 4);
     C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603)].
  Definition hdr_W (S SPA F0 lo : Z) : list (Z * Z) :=
    [(F0, F0 + 64); (Z.shiftr F0 3 + 2147450880, Z.shiftr F0 3 + 2147450880 + 8); (lo, SPA + 568); (S + 8, S + 12)].

  Definition inf_hdr1_stmt (PM : Z -> Prop) : Prop :=
    forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (payload : list Z)
      (zti zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total back was pad : word)
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word)
      (jA : list byte) (j0 j1 j2 flagp : word) (jk : list byte) (m : amem)
      (K : forall (v0 v8 v16 v24 v240 v328 v512 j544 j552 : word) (y6 y7 y10 y11 y12 y13 y14 y16 y19 y21 y22 y23 y26 y28 y29 y30 y31 : word) (m' : amem),
         rw_cells bsegs m' (l_SPA ly) (inf_locals (c_p cx) (l_Zs ly) (l_F0 ly) v0 v8 v16 v24 v240 (Z_to_bv 64 0) v328 (Z_to_bv 64 (c_n cx - t_cin st))
                                                  (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (c_ob cx + t_cout st)) (Z_to_bv 64 (c_osz cx - t_cout st))
                                                  v512 (Z_to_bv 64 (c_q cx + t_cin st)) j544 j552) ->
         rw_cells bsegs m' (c_p cx) (istate_cells (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (mode_load (t_mode st))) (Z_to_bv 64 (t_last st)) (Z_to_bv 64 5) havedict
                                       (Z_to_bv 64 (t_flags st)) dmax check total (Z_to_bv 64 0) (Z_to_bv 64 15) (Z_to_bv 64 (wsz cx))
                                       (Z_to_bv 64 (t_whave st)) (Z_to_bv 64 (t_wnext st)) (Z_to_bv 64 (c_w cx))
                                       (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 (t_bits st))
                                       (Z_to_bv 64 (t_length st)) (Z_to_bv 64 (t_offset st)) (Z_to_bv 64 (t_extra st))
                                       (Z_to_bv 64 (cp_addrA (c_p cx) (t_lc st))) (Z_to_bv 64 (cp_addrA (c_p cx) (t_dc st)))
                                       (Z_to_bv 64 (t_lb st)) (Z_to_bv 64 (t_db st)) (Z_to_bv 64 (t_ncode st)) (Z_to_bv 64 (t_nlen st))
                                       (Z_to_bv 64 (t_ndist st)) (Z_to_bv 64 (t_shave st)) (Z_to_bv 64 (c_p cx + 1384 + 4 * t_nx st))) ->
         rw_cells bsegs m' (l_F0 ly) (F0_cells jk flagp) -> rw_cells bsegs m' (Z.shiftr (l_F0 ly) 3 + 2147450880) F0_shadow ->
         munch (hdr_W (c_p cx) (l_SPA ly) (l_F0 ly) (l_lo ly)) m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> stk bsegs m' (l_lo ly) (l_SPA ly) ->
         evtF bsegs RNG POST (DISP_MS cx ly gp tp FR fc (st_load cx st) y6 y7 y10 y11 y12 y13 y14 y16 y19 y21 y22 y23 y26 y28 y29 y30 y31 m')),
    PM (t_mode st) ->
    inf_ctx cx ly AI RNG LB -> AHEAP AI L RNG stA LB m ->
    ainv cx st lf cf ->
    inf_emem cx (l_Zs ly) st lf cf wf fo payload zti zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total back was pad m ->
    rw_cells bsegs m (l_SPA ly) (chop (repeat SH8 71) jA) ->
    rw_cells bsegs m (l_F0 ly) [C8 j0; C8 j1; C8 j2; CB 32 jk; C8 flagp] ->
    rw_cells bsegs m (Z.shiftr (l_F0 ly) 3 + 2147450880) [C8 (Z_to_bv 64 0)] ->
    rng RNG (l_F0 ly) 64 -> rng RNG (Z.shiftr (l_F0 ly) 3 + 2147450880) 8 ->
    shadow_bytes m (Z.shiftr (l_Zs ly) 3 + 2147450880) (Z.shiftr (l_Zs ly) 3 + 2147450880 + 14) (fun _ => 0) ->
    shadow_bytes m (Z.shiftr (c_p cx) 3 + 2147450880) (Z.shiftr (c_p cx) 3 + 2147450880 + 897) (fun _ => 0) ->
    stk bsegs m (l_lo ly) (l_SPA ly) -> mem_inv bsegs m ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly)) (Z_to_bv 64 (l_F0 ly)) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 0) x20 (Z_to_bv 64 2147450880) x22 x23 x24 x21 x26 x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x8de10) fc None m (seg_rom bsegs)).
End S.
End CANSEC1.
