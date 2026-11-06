(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict Refund Lazyiq4 Fixej5z EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARtStmts ARtSscs ARtSf1m.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AInv ALogic AMTac AMallocI ANodeA7 ANodeA6 ANodd09 ASecComb ACor4x6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

Section G2S.
Context {Clg : Ceiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sec_grant2_stmt : Prop :=
  forall (rac spa gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AState) (n lo hi stkobj canfill : Z) (key : list Z) (T1 : TSet),
    let v := aview_of (pa_hull A) m in let sa := bv_unsigned spa in let thr := p_thr (a_pl A) in
    @pa_ainv _ DepotRepL A m md ->
    kMaxPrimaryUser < n < 524288 ->
    sa mod 16 = 0 -> 0 <= canfill <= 1 ->
    alloc_ceiling <= lo -> lo <= sa - 4096 -> sa <= hi <= 2^47 -> mapped v lo (hi - lo) ->
    sa <= stkobj /\ stkobj + 2064 <= hi ->
    ro_cells rsegs v stkobj [C8 (wz (stkobj + 16)); C8 (wz (Z.of_nat (length key)))] ->
    bytes_at rsegs v (stkobj + 16) (u64s (map (Z_to_bv 64) key)) ->
    In key (p_dkeys (a_pl A)) -> Forall (fun w => 0 <= w < 2^64) key ->
    as_livebytes A + n <= LIVE_MAX -> as_nlive A + 1 <= NLIVE_MAX -> 1 <= as_seccred A ->
    lma_mid_stmt -> lma_tail_stmt -> thread_stats_stmt -> poison_stmt -> poison0_stmt -> depot_put_stmt depot_repL ->
    lma_esp_stmt -> mapfixed_pre_stmt -> lma_espost_stmt ->
    alloc_core_K1v rac spa gp (cl_tp LPA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A n canfill lo hi T1 ->
    forall (m1 : mem) (md1 : Model) (t0' t1' t2' a6' t3' t4' t5' t6' : word) (junk0 scrL scrM : list byte),
    munch [(lo, sa)] v m1 -> wmono rsegs v m1 -> mem_inv rsegs m1 -> stk rsegs m1 lo (sa + -128 + -48 + -96 + -48) ->
    MInv (pa_hull A) (pa_lhull A) (pa_eager A) md1 -> same_but_materialized md md1 ->
    (forall a, hidc (pa_hull A) a = true -> m1 a = None) ->
    rw_cells rsegs m1 (sa + -128) (alloc_s1a_frame spa canfill s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 rac junk0) ->
    rw_cells rsegs m1 (sa + -128 + -48) (comb_frame (wz (rz_size n)) (wz (needed_size2 n)) (wz 8) (wz n) (wz 0) (wz 0x3731c)) ->
    rw_cells rsegs m1 (sa + -128 + -48 + -96)
         (lma_frame scrL (wz 7) (wz (-8)) (wz stkobj) (wz 0xb1558) (wz n) (wz (rz_size n)) (wz (needed_size2 n)) (wz 8) (wz n) (wz 8) (wz comb_sec_ret)) ->
    rw_cells rsegs m1 (sa + -128 + -48 + -96 + -48) [CB 12 scrM; C4 (wz 34); C8 (wz (map_size n)); C8 (wz ASecComb.LMA); C8 (wz ASecComb.LSTAT); C8 (wz lma_mapret)] ->
    forall mbw : word,
    grant_okf (wz 34) (wz 0) md1 mbw (map_size n) = true ->
    Z.of_nat (length (sr_chunks (a_sec A))) = 0 /\ sr_reserved (a_sec A) = 0 ->
    srealizes (cl_segs LPA)
      (mkCfg (MS (mkR (wz mmapordie_resume) (wz (sa + -128 + -48 + -96 + -48)) gp (cl_tp LPA) t0' t1' t2'
                      (wz lma_name) (wz (map_size n)) mbw (wz (map_size n)) (wz 3) (wz 34) (wz (-1)) (wz 0) a6' (wz 222)
                      (wz ANodeA7.PSC) (wz (needed_size2 n)) (wz (rz_size n)) (wz 8) (wz 0xb1558) (wz stkobj) (wz 7) (wz 7) (wz thr) (wz 1)
                      t3' t4' t5' t6')
                 F (wz ANodeA7.mmap_after_pc) fc None (apply_zeros (munrestrict (hidc (pa_hull A)) m m1) [(mbw, wz (map_size n))]) (seg_rom (cl_segs LPA)))
             (grant_model (wz 34) mbw (wz (map_size n)) false md1)) T1.
End G2S.
