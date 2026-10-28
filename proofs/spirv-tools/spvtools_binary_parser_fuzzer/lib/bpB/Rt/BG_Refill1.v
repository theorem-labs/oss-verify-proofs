(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BllocRepFacts BllocRepFacts2 BllocWalkKit BW_LargeAlloc1 BW_Efs BG_Malloc BG_WFHit BG_RefillModel BS_Refill1.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section RefillCells.
  Context {HCEIL : HeapCeil}.
  Variables (s : ast) (m : mem) (c : Z).
  Hypothesis R : AREP s m.
  Hypothesis HC : 1 <= c <= 30.
  Let st := a_st s.
  Let T := a_thr s.
  Let CA := a_cache s.
  Let P := CA + PCLASS_SIZE * c.
  Let RI := a_ri s + REGIONINFO_SIZE * c.
  Let r := get_region st c.
  Hypothesis EMPTY : pc_count (get_pc st c) = 0.

  Let OK : ast_ok s. Proof. exact (proj1 R). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OK). Qed.
  Let WFs : WF st. Proof. exact (proj2 OK). Qed.
  Let RO : region_ok st c. Proof. apply WF_region; [exact WFs| unfold kNumClasses; lia]. Qed.
  Let CO : cache_ok st c. Proof. apply WF_cache; [exact WFs| unfold kNumClasses; lia]. Qed.
  Let CT : 32 <= class_size c <= 65536 /\ class_size c mod 32 = 0. Proof. pose proof (class_size_table_facts c ltac:(lia)) as X. repeat split; try lia. Qed.

  Lemma refill_pure :
       0 <= rg_num_freed r /\ 4 * rg_num_freed r <= rg_mapped_free_array r <= kFreeArraySize
    /\ rg_mapped_free_array r mod kFreeArrayMapSize = 0
    /\ 0 <= rg_allocated_user r <= rg_mapped_user r /\ rg_mapped_user r + kUserMapSize <= kFreeArrayOffset
    /\ rg_mapped_user r mod kUserMapSize = 0
    /\ length (rg_free_array r) = Z.to_nat (rg_num_freed r)
    /\ Z.of_nat (length (wlist (rev (rg_free_array r)))) = rg_num_freed r
    /\ rg_mapped_user r - rg_allocated_user r < class_size c + kUserMapSize
    /\ class_size c * rg_num_freed r <= rg_allocated_user r
    /\ pc_chunks (get_pc st c) = [].
  Proof.
    pose proof (ro_alloc_nonneg _ _ RO) as X1. pose proof (ro_alloc_le _ _ RO) as X2. pose proof (ro_mapped_mod _ _ RO) as X3. pose proof (ro_mapped_bound _ _ RO) as X4.
    pose proof (ro_tail_small _ _ RO ltac:(lia)) as TS. pose proof (ro_numfreed _ _ RO) as NF. pose proof (ro_fa_le _ _ RO) as X5. pose proof (ro_fa_mod _ _ RO) as X6.
    pose proof (ro_fa_bound _ _ RO) as X7.
    pose proof (free_array_count st c WFs ltac:(unfold kNumClasses; lia) ltac:(lia)) as FC.
    pose proof (co_count _ _ CO) as CC. fold st in X1, X2, X3, X4, X5, X6, X7, TS, NF, FC, CC. fold r in X1, X2, X3, X4, X5, X6, X7, TS, NF, FC, CC. rewrite EMPTY in CC.
    assert (LEN : length (rg_free_array r) = Z.to_nat (rg_num_freed r)) by (rewrite NF; unfold zlen; lia).
    assert (PCS : pc_chunks (get_pc st c) = []) by (destruct (pc_chunks (get_pc st c)); [reflexivity| rewrite zlen_cons in CC; unfold zlen in CC; lia]).
    assert (NF0 : 0 <= rg_num_freed r) by (rewrite NF; unfold zlen; lia).
    unfold wlist. rewrite length_map, length_rev, LEN, Z2Nat.id by exact NF0.
    repeat split; try assumption; try lia. destruct (rg_allocated_user r =? 0); lia.
  Qed.

  Lemma refill_cells_of_arep :
    exists (q0 q1 q2 q3 : word),
       rw_cells asegs m P [C4 (wz 0); C4 (wz (if as_cache_inited st then max_count c else 0))]
    /\ stk asegs m (P + 16) (P + 80)
    /\ (forall c', 1 <= c' <= 31 -> exists mc cs, rw_cells asegs m (CA + 80 * c' + 4) [C4 mc] /\ rw_cells asegs m (CA + 80 * c' + 8) [C8 cs]
                                   /\ (as_cache_inited st = true -> mc = wz (max_count c') /\ cs = wz (class_size c')))
    /\ rw_cells asegs m (T + 2768) [C8 q0; C8 q1; C8 q2; C8 q3] /\ stk asegs m (T + 2800) (T + 3168)
    /\ rw_cells asegs m RI [C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz (rg_num_freed r)); C8 (wz (rg_mapped_free_array r));
                            C8 (wz (rg_allocated_user r)); C8 (wz 0); C8 (wz (rg_mapped_user r)); C8 (wz 0)]
    /\ stk asegs m (RI + 64) (RI + 68) /\ rw_cells asegs m (RI + 68) [C1 (b8 0)] /\ stk asegs m (RI + 69) (RI + 128)
    /\ u32arr asegs m (FA s c) (wlist (rev (rg_free_array r)))
    /\ stk asegs m (FA s c + 4 * rg_num_freed r) (FA s c + rg_mapped_free_array r)
    /\ stk asegs m (RB s c + rg_allocated_user r) (RB s c + rg_mapped_user r)
    /\ RENV (wz ATP) ATSD (a_ctx s) T (a_sb s) (a_ri s) m.
  Proof.
    destruct R as (OK' & INST & FL & THR & SEC & IA & CL & CH & BT & BG).
    assert (Hc' : 0 <= c < kNumClasses) by (unfold kNumClasses; lia).
    destruct (CL c Hc') as (RG & PC & RSH & RJ).
    pose proof refill_pure as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8 & U9 & U10 & PCS).
    pose proof PL as (S1 & S2 & S3 & P1' & P2' & P3 & T1 & T2 & T3 & _).
    apply akobj_env in T2; [| unfold kPageSize; clear; lia].
    assert (RS : a_sb s <= RB s c /\ RB s c + 2^32 <= a_sb s + kSpaceSize /\ FA s c = RB s c + kFreeArrayOffset).
    { unfold RB, FA. rewrite free_array_base_eq. pose proof (region_in_space st c ltac:(lia)) as RS. fold st. change (as_space_beg st) with (a_sb s) in RS. lia. }
    acb. unfold AHI_LO, kSpaceSize, kPageSize, kFreeArraySize, kFreeArrayOffset, kUserMapSize in *.

    destruct PC as (Q1 & Q2 & QU & QJ). fold st CA P in Q1, Q2, QU, QJ. rewrite EMPTY, PCS in *.
    replace (negb (c =? 0)) with true in Q1, Q2 by (symmetry; apply Bool.negb_true_iff, Z.eqb_neq; lia). rewrite Bool.andb_true_r in Q1, Q2.

    destruct THR as (Tc & Ttid & Tthr & Tstk & T40 & Tsw & Ttq & Jtq & Jcs & Jst & Tunw). fold T CA in Tc, Tstk, T40, Tsw, Ttq, Jtq, Jcs, Jst, Tunw.
    unfold OT_CACHE, CACHE_STATS, OT_STATS, OT_UNWINDING, OT_TQ, PCLASS_SIZE, REGIONINFO_SIZE in *.
    assert (ECA : CA = T + 208) by reflexivity.
    pose proof (junk_stk' _ _ _ Jcs ltac:(lia) ltac:(lia) ltac:(lia)) as SCS.
    destruct (stk_cells _ _ _ SCS ltac:(lia)) as [js JS]. replace (CA + 2560 + (2800 - 208 - 2560) - (CA + 2560)) with 32 in JS by lia.
    change (Z.to_nat 32) with 32%nat in JS.
    apply (rw_cells_split_CB asegs _ _ [] 32 js [] [8;8;8;8]%nat) in JS; [| reflexivity]. cbn [mk_CB_cells app] in JS.
    destruct (rw_cells_CB8_C8 _ _ _ _ JS) as [w0 JS0].
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in JS0. destruct JS0 as [K0 JS1]. cbn [cells_size csize Nat.add] in JS1.
    destruct (rw_cells_CB8_C8 _ _ _ _ JS1) as [w1 JS1'].
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in JS1'. destruct JS1' as [K1 JS2]. cbn [cells_size csize Nat.add] in JS2.
    destruct (rw_cells_CB8_C8 _ _ _ _ JS2) as [w2 JS2'].
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in JS2'. destruct JS2' as [K2 JS3]. cbn [cells_size csize Nat.add] in JS3.
    destruct (rw_cells_CB8_C8 _ _ _ _ JS3) as [w3 K3].
    exists w0, w1, w2, w3.
    split; [exact Q1|].
    split. { replace (P + 16 + 4 * 0) with (P + 16) in QJ by lia. replace (64 - 4 * 0) with 64 in QJ by lia.
             replace (P + 80) with (P + 16 + 64) by lia. apply junk_stk'; [exact QJ| subst P CA; lia| subst P CA; lia| lia]. }
    split.
    { intros c' Hc2. destruct (CL c' ltac:(unfold kNumClasses; lia)) as (_ & PC' & _). destruct PC' as (V1 & V2 & _).
      fold st CA in V1, V2. unfold PCLASS_SIZE in V1, V2.
      replace (negb (c' =? 0)) with true in V1, V2 by (symmetry; apply Bool.negb_true_iff, Z.eqb_neq; lia). rewrite Bool.andb_true_r in V1, V2.
      apply (proj1 (rw_cells_app asegs _ _ [_] _)) in V1. destruct V1 as [_ V1]. cbn [cells_size csize Nat.add length] in V1.
      replace (CA + 80 * c' + Z.of_nat 4) with (CA + 80 * c' + 4) in V1 by lia.
      eexists _, _. split; [exact V1|]. split; [exact V2|]. intros INI. rewrite INI. split; reflexivity. }
    split. { replace (T + 2768) with (CA + 2560) by lia.
             apply (proj2 (rw_cells_app asegs _ _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add].
             apply (proj2 (rw_cells_app asegs _ _ [_] _)). split; [exact K1|]. cbn [cells_size csize Nat.add].
             apply (proj2 (rw_cells_app asegs _ _ [_] _)). split; [exact K2|]. cbn [cells_size csize Nat.add]. exact K3. }
    split. { replace (T + 3168) with (T + 2800 + (3168 - 2800)) by lia. apply junk_stk'; [exact Jst| lia| lia| lia]. }

    destruct RG as (G1 & G2 & G3 & G4 & G5 & G6 & G7). fold st in G1, G2, G3, G4, G5, G6, G7. fold r in G1, G2, G3, G4, G5, G6, G7. fold RI in G1, G2, G3, G4.
    assert (ERI : RI = a_sb s + 137438953472 + 128 * c) by (subst RI; unfold a_ri, kSpaceSize; lia).
    split; [exact G1|].
    split. { replace (RI + 68) with (RI + 64 + 4) by lia. apply junk_stk'; [exact G2| lia| lia| lia]. }
    split; [exact G3|].
    split. { replace (RI + 128) with (RI + 69 + 59) by lia. apply junk_stk'; [exact G4| lia| lia| lia]. }
    split; [exact G5|].
    split. { replace (FA s c + rg_mapped_free_array r) with (FA s c + 4 * rg_num_freed r + (rg_mapped_free_array r - 4 * rg_num_freed r)) by lia.
             apply junk_stk'; [exact G6| lia| lia| lia]. }
    split. { replace (RB s c + rg_mapped_user r) with (RB s c + rg_allocated_user r + (rg_mapped_user r - rg_allocated_user r)) by lia.
             apply junk_stk'; [exact G7| lia| lia| lia]. }

    destruct INST as (A1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A9).
    destruct FL as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27).
    pose proof A1 as A1'.
    apply (proj1 (rw_cells_app asegs _ _ [_;_;_] _)) in A1. destruct A1 as [ISB A2]. cbn [cells_size csize Nat.add length] in A2.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in A2. destruct A2 as [IRI A3]. cbn [cells_size csize Nat.add length] in A3.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in A3. destruct A3 as [PMH _].
    unfold AINST, OI_SPACEBEG, AFLAGS, ACFLAGS, ASHBASE_CELL, ASHADOW_BASE, AHIGHMEMEND, ACANPOISON, AINITED, ACTXSIZE, ATSDINIT,
           AALLOCFLAGS, AHOOKS, AREALMEMSET, AMEMSET, AGOT_LO, APAGESZ, ASECNAME, ATLSSLOT, ATSD, ALSANDIS, AGOT2 in *.
    cbn [Z.of_nat Z.add Pos.add Nat.add] in IRI, PMH.
    constructor.
    - constructor; assumption.
    - exact ISB.
    - exact IRI.
    - exact PMH.
  Qed.
End RefillCells.
