(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BllocRepFacts BllocRepX BsDepotInv BW_AllocBase BW_MallocBase BllocWalkKit BW_LargeAlloc1 BW_PoisonRemap1 BG_Malloc.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section LargeCells.
  Context {HCEIL : HeapCeil}.
  Variables (s : ast) (m : mem).
  Hypothesis R : AREP s m.
  Let st := a_st s.

  Lemma senv_of_arep : SENV (wz ATP) ATSD (a_ctx s) (a_thr s) m.
  Proof.
    destruct R as (OK & INST & FL & THR & _).
    destruct FL as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27).
    destruct THR as (T1 & T2 & T2b & _).
    unfold AFLAGS, ACFLAGS, ASHBASE_CELL, ASHADOW_BASE, AHIGHMEMEND, ACANPOISON, ATSDINIT, AREALMEMSET, AMEMSET, AGOT_LO, APAGESZ, ASECNAME, ATLSSLOT, ATSD in *.
    constructor; try assumption; unfold wz, ATP; rewrite ?unsigned_lit by lia; assumption.
  Qed.

  Lemma large_cells_of_arep :
       rw_cells asegs m (AINST + 64) [C8 (wz 4096); C8 (wz (a_pa s)); C8 (wz (a_pa s))]
    /\ rw_cells asegs m (AINST + 112) [C8 (wz (as_n_reserved st)); C8 (wz (zlen (as_sec st))); C8 (wz 0)]
    /\ stk asegs m (AINST + 136) (AINST + 680)
    /\ rw_cells asegs m (AINST + 680) [C8 (wz 0)]
    /\ stk asegs m (AINST + 688) (AINST + 728)
    /\ stk asegs m (a_thr s + 2800) (a_thr s + 3168)
    /\ rw_cells asegs m (a_thr s + 3168) [C1 (b8 0)]
    /\ u64arr asegs m (a_pa s) (wlist (map sc_map_beg (as_sec st)))
    /\ stk asegs m (a_pa s + 8 * zlen (as_sec st)) (a_pa s + 8 * as_n_reserved st)
    /\ 0 <= zlen (as_sec st) <= as_n_reserved st /\ (as_n_reserved st = 0 \/ as_n_reserved st = kChunksBlockCount).
  Proof.
    destruct R as (OK & INST & FL & THR & SEC & _).
    destruct INST as (A1 & J1 & A2 & J2 & A3 & J3 & J4 & _).
    destruct THR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Jst & Tunw).
    destruct SEC as (U & J & _).
    destruct OK as [PL W]. pose proof W as W'. destruct W' as (_ & _ & _ & _ & _ & _ & Wn & Wr & _).
    pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & _).
    apply akobj_env in T2; [| unfold kPageSize; clear; lia]. apply aapp_env in P2; [| unfold kPtrArrayReserve; clear; lia].
    assert (NN : 0 <= zlen (as_sec (a_st s))) by (unfold zlen; lia).
    unfold OI_SPACEBEG, OI_NRESERVED, OI_SECMUTEX, OI_GSTATS, OI_Q, OT_STATS, OT_UNWINDING, AINST in *.
    acb. unfold AHI_LO, kPtrArrayReserve, kPageSize, kChunksBlockCount in *. unfold st.
    apply (rw_cells_app asegs _ _ [C8 (wz (a_sb s)); C4 (wz 4294967295); C4 (wz 0); C8 (wz (a_ri s)); C8 (wz 0)] [C8 (wz 4096); C8 (wz (a_pa s)); C8 (wz (a_pa s)); C8 (wz 8388608)]) in A1.
    destruct A1 as [_ A1]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in A1.
    apply (rw_cells_app asegs _ _ [C8 (wz 4096); C8 (wz (a_pa s)); C8 (wz (a_pa s))] [C8 (wz 8388608)]) in A1. destruct A1 as [A1 _].
    replace (1628632 + 32 + 32) with (1628632 + 64) in A1 by lia.
    split; [exact A1|]. split; [exact A2|].
    split; [pose proof (junk_stk' _ _ _ J2 ltac:(lia) ltac:(lia) ltac:(lia)) as K; replace (1628632 + 136 + (680 - 136)) with (1628632 + 680) in K by lia; exact K|].
    split; [exact A3|].
    split; [pose proof (junk_stk' _ _ _ J3 ltac:(lia) ltac:(lia) ltac:(lia)) as K; replace (1628632 + 688 + (728 - 688)) with (1628632 + 728) in K by lia; exact K|].
    split; [pose proof (junk_stk' _ _ _ Jst ltac:(lia) ltac:(lia) ltac:(lia)) as K; replace (a_thr s + 2800 + (3168 - 2800)) with (a_thr s + 3168) in K by lia; exact K|].
    split; [exact Tunw|]. split; [exact U|].
    split; [pose proof (junk_stk' _ _ _ J ltac:(lia) ltac:(lia) ltac:(lia)) as K;
           replace (a_pa s + 8 * zlen (as_sec (a_st s)) + 8 * (as_n_reserved (a_st s) - zlen (as_sec (a_st s)))) with (a_pa s + 8 * as_n_reserved (a_st s)) in K by lia; exact K|].
    unfold kChunksBlockCount in Wr. lia.
  Qed.
End LargeCells.
