(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg AProto ABase AQConst.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AKit AKit2.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma run_free_hooks_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (lo : Z),
stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 32 ->
mem_inv asegs m ->
rw_cells asegs m AFHOOK [C8 (Z_to_bv 64 0)] ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
evtF asegs RNG (fun ms' => exists m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x61020) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros ST CEIL LO MI HK RIMG RSTK. unfold AFHOOK in *.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
word_range sp SPR.
Local Ltac2 Set LiaHints.tbl := fun () => "00M0>11805467289.5511805467289.5711805467289.5817221588796.5519006120615.5819007305966.5523230285244.5723814431342.5725566553219.5833680001082.5534290115814.4938806986883.5538806986883.5639939554818.5041564619544.4943061431595.4743987951407.5745221239098.5849840447350.555012112366.58 5180980284.58 53767577772.5654618151079.5755104759171.57563227834.57  6166287527.55 63235321901.5463235321901.556613537782.55 00000100200300700800A00E00N00O00T00U00V00W00[00\00`00d00i00j01301701;01<01=01B01C01G01K01LSSSS2HBSS4CEIL2LOS2HBS4CEIL2LOSS3SPRSSSS2LOSS2LOS2LOS3SPRSS4CEIL2LOS2HBS2LOSSS3SPRSS2LOS2LOS".
carve_frame 32%nat ST.
do 4 step.
step.
step. step. step.
step. if_lit.
step. step. step.
step. zstep. step. step. if_lit.
step.
do 5 step.
release_frame FR ST (bv_unsigned sp). finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
