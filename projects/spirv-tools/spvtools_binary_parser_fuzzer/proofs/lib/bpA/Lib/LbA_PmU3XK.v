(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HTac HArr HSysStep HExec CellsX TacX HMem HMState HLFrame.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPrelim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsStack0 RtA_Iface AW_MallocBase.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_Kit LbA_Bridge LbA_Conv LbA_SR LbA_FKit LbA_MILB LbA_PrsStmt LbA_Own LbA_PmBase LbA_FSlots LbA_PmOwn LbA_PmCut LbA_PmTac LbA_PmHex.
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
    PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> pmw_okA H w -> 0 <= k -> k + 4 <= 1216 ->
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
End XK.
