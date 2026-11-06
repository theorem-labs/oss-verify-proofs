(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg AProto ABase AQConst.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import AKit AKit2.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma run_free_hooks_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 32 ->
  mem_inv bsegs m ->
  rw_cells bsegs m AFHOOK [C8 (Z_to_bv 64 0)] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (fun ms' => exists m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5fe20) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST CEIL LO MI HK RIMG RSTK. unfold AFHOOK in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  word_range sp SPR.
  Local Ltac2 Set LiaHints.tbl := fun () => "00M0>11805467289.5511805467289.5711805467289.5817221588796.5519006120615.5823230285244.5725566553219.5833680001082.5534140524150.5534290115814.4938806986883.5538806986883.5639101754358.5539939554818.5041564619544.4943061431595.4743987951407.5745221239098.585180980284.58 53767577772.5654569212142.5554618151079.5755104759171.57563227834.57  59382628974.576166287527.55 63235321901.5463235321901.5567663283182.5800000100200300700800<00=00B00C00D00E00F00G00K00L00P00T00Y00]00a00j00k00l01101:01;01?01C01LSSSS2HBSS2HBSS3SPRSSSSSS2LOSS2LOS2LOS3SPRS2HBS2LOS4CEIL2LOSSS3SPRS4CEIL2LOSS2LOS2LOS4CEIL2LO".
carve_frame 32%nat ST.
  do 4 step.                                   (* [comment removed for export] *)
  step.                                        (* [comment removed for export] *)
  step. step. step.                            (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  step. step. step.                            (* [comment removed for export] *)
  step. zstep. step. step. if_lit.            (* [comment removed for export] *)
  step.                                        (* [comment removed for export] *)
  do 5 step.                                   (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
