(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg AProto ABase.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AKit.
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
Definition rz2log_post (res : Z) (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : amem) : machine_state -> Prop :=
fun ms' => exists a1 a2 a3 a4 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp).
#[using="Type"] Lemma rz2log16_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (lo : Z),
stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 16 ->
mem_inv asegs m ->
a0 = Z_to_bv 64 16 ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
evtF asegs RNG (rz2log_post 0 ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x377f8) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros ST CEIL LO MI -> RIMG RSTK. atop_facts.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
word_range sp SPR.
Local Ltac2 Set LiaHints.tbl := fun () => "00@0>11805467289.5520433961190.4821212737002.6124972240369.6131399144472.4832600174396.5536789963889.613830427394.49 43061431595.4645221239098.5554164510851.5554164510851.5657293592682.6163235321900.5463235321900.5567081926311.5500000100200300400500900:00>00B00G00H00I00J00N00R00SSSSSSS2HBSS2LOS2LOS3SPRSSSS2LOS2LOS".
carve_frame 16%nat ST.
do 2 step.
zstep. step. zstep. step. if_lit.
step. zstep. step. if_lit.
zstep. zstep. step. if_lit.
zstep. step. step. step. zstep. zstep. zstep. zstep. zstep.
lstep. zstep. step. step. if_lit.
step. zstep. step. if_lit.
do 4 step.
release_frame FR ST (bv_unsigned sp). finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rz2log2048_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (lo : Z),
stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 16 ->
mem_inv asegs m ->
a0 = Z_to_bv 64 2048 ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
evtF asegs RNG (rz2log_post 7 ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x377f8) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros ST CEIL LO MI -> RIMG RSTK. atop_facts.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
word_range sp SPR.
Local Ltac2 Set LiaHints.tbl := fun () => "00@0>11805467289.5520433961190.4824972240369.6131399144472.4832394322977.6132600174396.553341391738.61 3830427394.49 43061431595.4645221239098.5554164510851.5554164510851.5657293592682.6163235321900.5463235321900.5567081926311.5500000100200300400500900:00>00B00G00H00I00J00N00R00SSSSSSS2HBSS2LOS2LOS3SPRSSSS2LOS2LOS".
carve_frame 16%nat ST.
do 2 step.
zstep. step. zstep. step. if_lit.
step. zstep. step. if_lit.
zstep. zstep. step. if_lit.
zstep. step. step. step. zstep. zstep. zstep. zstep. zstep.
lstep. zstep. step. step. if_lit.
step. zstep. step. if_lit.
do 4 step.
release_frame FR ST (bv_unsigned sp). finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition ARSSLIM : Z := 0x1246e2.
#[using="Type"] Lemma rss_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem),
rw_cells asegs m ARSSLIM [C1 (Z_to_bv 8 0)] ->
rng_aimg RNG ->
evtF asegs RNG (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x5ed48) fc None m (seg_rom asegs)).
Proof.
intros until m. intros C RIMG. unfold ARSSLIM in *.
step. Local Ltac2 Set LiaHints.tbl := fun () => "0020>39213690267.3853510313878.44000001002SS".
lstep. zstep. step. apply evtF_done. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma can_poison_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem),
rw_cells asegs m ACANPOISON [C1 (Z_to_bv 8 1)] ->
rng_aimg RNG ->
evtF asegs RNG (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x54160) fc None m (seg_rom asegs)).
Proof.
intros until m. intros C RIMG. unfold ACANPOISON in *.
step. Local Ltac2 Set LiaHints.tbl := fun () => "0030>52523015478.4453510313878.4465250765371.38000001002003SSS".
lstep. step. zstep. step. apply evtF_done. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition ALSAN_TLSOFF : Z := 0x9a3d8.
Definition ALSAN_CNT : Z := 0x5d5420.
#[using="Type"] Lemma lsan_disabled_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem),
tp = Z_to_bv 64 ATP ->
rw_cells asegs m ALSAN_TLSOFF [C8 (Z_to_bv 64 0x10)] ->
rw_cells asegs m ALSAN_CNT [C4 (Z_to_bv 64 0)] ->
rng_aimg RNG ->
evtF asegs RNG (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x80354) fc None m (seg_rom asegs)).
Proof.
intros until m. intros -> C1 C2 RIMG. unfold ALSAN_TLSOFF, ALSAN_CNT, ATP in *.
step. step. zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0020>53510313878.4461471995341.38000001002SS".
lstep. zstep. step. apply evtF_done. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition AMHOOKS : Z := 0x133f40.
#[using="Type"] Lemma run_malloc_hooks_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (lo : Z),
stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 32 ->
mem_inv asegs m ->
rw_cells asegs m AMHOOKS [C8 (Z_to_bv 64 0)] ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
evtF asegs RNG (fun ms' => exists a0' a2' m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x60f64) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros ST CEIL LO MI HK RIMG RSTK. unfold AMHOOKS in *.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
word_range sp SPR.
Local Ltac2 Set LiaHints.tbl := fun () => "00U0>11805467289.5511805467289.5611805467289.5711805467289.5814782759150.5515685060272.5617221588796.5517776320428.5617776320429.5519006120615.5823230285244.5725435258127.5625435258127.5725566553219.5833680001082.5534290115814.4938806986883.5538806986883.5639939554818.5041564619544.4942831019478.5643061431595.4743987951407.5745221239098.585180980284.58 53767577772.5654618151079.5755104759171.5756289563638.55563227834.57  59178106163.566166287527.55 63235321901.5463235321901.5566656729710.5768309604434.56802261998.58  00000100200300400=00A00E00I00M00N00R00S00T00U00Z00[00\00]00a00b00g00k00o01401801<01=01>01?01D01E01F01J01N01W01`01iSSSSS4CEIL2LOS2HBS2HBS2LOS2LOSS2HBSSSS3SPRSSSS2LOSS3SPRS2LOS2LOS3SPRS2HBS2LOSSSS3SPRSSS2LOS2LOS4CEIL2LOS4CEIL2LOS4CEIL2LO".
carve_frame 32%nat ST.
do 5 step.
do 2 step.
step. step.
step. zstep. step. step. if_lit.
do 6 step.
release_frame FR ST (bv_unsigned sp). finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
