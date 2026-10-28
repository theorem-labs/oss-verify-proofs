(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface BW_MallocBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHex LbB_PmGlue.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Lemma cb4_as_c4 : forall m A (bs : list byte), length bs = 4%nat -> rw_cells asegs m A [CB 4 bs] ->
  rw_cells asegs m A [C4 (Z_to_bv 64 (bytes_le_to_Z bs))] /\ 0 <= bytes_le_to_Z bs < 2 ^ 32.
Proof.
  intros m A bs L RW. pose proof (bytes_le_to_Z_range4 bs L) as R. split; [| exact R].
  destruct RW as [[WF BA] WR]. cbn [cells_bytes cbytes app] in BA. rewrite app_nil_r in BA. cbn [cells_size csize] in WR.
  split; [split|].
  - cbn. split; exact Logic.I.
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r. unfold le4. rewrite u64_of_Z by lia.
    rewrite <- L. rewrite Z_to_le_bytes_to_Z. exact BA.
  - cbn [cells_size csize]. exact WR.
Qed.

Section XK.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable LINV : mem -> Prop.

  Lemma rf_cell4_junk : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal k,
    PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> pmw_okA H w -> 0 <= k -> k + 4 <= 832 ->
    exists x, 0 <= x < 2 ^ 32 /\ rw_cells asegs m (wa_s1 w + k) [C4 (Z_to_bv 64 x)].
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal k X OK Hk Hk4.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as STK.
    pose proof (wr_at_of_stk asegs m (wa_lo w) (wa_sp0 w) STK) as W. destruct W as (W0 & W1 & W2).
    assert (WR : wr_at asegs m (wa_s1 w + k) 4).
    { split; [lia|]. split; [lia|]. intros i Hi. replace (wa_s1 w + k + i) with (wa_lo w + (wa_s1 w + k + i - wa_lo w)) by lia. apply W2. lia. }
    destruct (rw_cells_of_wr_hi m (wa_s1 w + k) 4 WR ltac:(unfold AIMG_TOP, AFS_HDR in *; lia) ltac:(lia)) as (bs & RB).
    change (Z.to_nat 4) with 4%nat in RB.
    assert (L : length bs = 4%nat).
    { destruct RB as [[WF _] _]. destruct WF as [C _]. cbn in C. exact C. }
    destruct (cb4_as_c4 m _ bs L RB) as [C R]. exists (bytes_le_to_Z bs). split; [exact R | exact C].
  Qed.

  Lemma ff_cell4_junk : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal k,
    PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> pmw_okA H w -> 0 <= k -> k + 4 <= 16384 ->
    exists x, 0 <= x < 2 ^ 32 /\ rw_cells asegs m (wa_ff w + k) [C4 (Z_to_bv 64 x)].
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal k X OK Hk Hk4.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    destruct (ff_junk H LINV w s LB LBs m mo c ins tbl ftbl TB spal k 4 X ltac:(unfold AIMG_TOP, AFS_HDR in *; lia) Hk ltac:(lia) Hk4) as (bs & RB).
    change (Z.to_nat 4) with 4%nat in RB.
    assert (L : length bs = 4%nat).
    { destruct RB as [[WF _] _]. destruct WF as [C _]. cbn in C. exact C. }
    destruct (cb4_as_c4 m _ bs L RB) as [C R]. exists (bytes_le_to_Z bs). split; [exact R | exact C].
  Qed.
End XK.
