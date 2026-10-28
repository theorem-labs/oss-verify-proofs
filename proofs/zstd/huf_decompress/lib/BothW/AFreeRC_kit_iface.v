(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA StepF SysStepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto ABase ABytes AQConst AKitQ AMalloc_iface ADepot_iface ARep ARepQ ARepQP ARepQR ARepQD ALayout AHeapP ARepKit ARepFrame
     AKit AKit2 AModelFacts ASec AFreeModel AFreeRep AFreeGeo AFreeRead F_afree_tail F_afree_icpt F_afreeC_iface F_afree_arep F_afree_arepR
     ARecGeo F_adorec AQrecP AFreeC_kit_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Set Keyed Unification.   (* [comment removed for export] *)
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Variable CI : list (Z * Z).

(* [comment removed for export] *)
Definition store_freeRC_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (s : astate) (LB : list ablock) (X : aconc) (Q : qconc) (c k n b1 ctx lo k24 : Z)
         (l1 l2 : list xbusy) (stj : word) (chunks : list word),
  let ch := CPrim c n in
  let sq := st_enq s ch in
  let ek := ek_of L s X Q n k24 stj chunks in
  let g := g_of L s Q (ek_delta ek n) in
  alayout_ok L -> arng L RNG s -> AREP (AHQm DI ASEC_of AFK Q) L s X m -> ablocks L s X LB -> AFK L LB m ->
  x_busy X = l1 ++ bquar c k n b1 ctx :: l2 -> 1 <= n ->
  (exists pend, q_pend Q = (c, k) :: pend) ->
  enq_is_app s = false ->
  nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls s K_BATCH_CLASS) - 1)) = Some k24 ->
  busy_of X K_BATCH_CLASS k24 = None -> 0 <= k24 < ndist s K_BATCH_CLASS ->
  ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q)) ->
  junk_at m (abatch_addr L k24) 8192 -> fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa ->
  a_cinit s = true -> 0 < c_count (get_cls s K_BATCH_CLASS) ->
  Q_CACHE < a_qloc_bytes sq -> Q_MAX < a_qglob_bytes sq + a_qloc_bytes sq ->
  ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc s))) (qlast L (q_loc Q)) n (fhm L c k n) m ->
  dk_preC ek g RNG (al_t L) (qlast L (q_loc Q)) (fhm L c k n) (a_qloc_bytes s + ek_delta ek n) m ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK -> tp = Z_to_bv 64 ATP ->
  forall ms1,
    free_torec_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) (fhm L c k n) n
                    (Z.of_nat (length (a_qloc s))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes s) b1 ctx lo m ms1 ->
    storeC_post DI AFK CI L RNG ek g ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (st_after sq) LB (al_t L) lo m ms1.
End S.
End CANSEC1.
