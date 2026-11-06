(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg AProto ABase.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import AKit AModelFacts F_aunwind F_aalloc_s F_acache.
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
Definition allocate_entry := 0x32388%Z.
#[using="Type"] Lemma rz_ladder_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (n : Z),
0 <= n < 2^40 ->
rng_aimg RNG ->
evtF bsegs RNG (fun ms' => exists a0',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (rz_log n)) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x324f4) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 49) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x32420) fc None m (seg_rom bsegs)).
Proof.
intros until n. intros N RIMG. unfold rz_log.
step. Local Ltac2 Set LiaHints.tbl := fun () => "00F0>28866468740.3836000989678.4038917905716.5140675739649.4141855593050.444354982892.38 52673946479.3958887966598.4060091000683.4361929812114.3861929812241.3961929812368.4061929812503.4161929812630.4261929812757.4361937685140.5162248037993.416231347328.42 63935938706.446396461315.43 67570755847.399880917736.42 00000400800900=00A00E00I00M00Q00T00W00Z00]00`00c00f00j00n01201601:01>S2K0S2K2SS2K3S2K6S2K0S2K1S2K2S2K5S1NS1NS1NS1NS1NS1NS1NS2K3S2K4S2K6S2K5S2K1S2K4".
if_cases K0; zify_cond K0.
2: { replace (n <=? 48) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
replace (n <=? 48) with false by (symmetry; apply Z.leb_gt; lia).
step. step. if_cases K1; zify_cond K1.
2: { replace (n <=? 96) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
replace (n <=? 96) with false by (symmetry; apply Z.leb_gt; lia).
step. step. if_cases K2; zify_cond K2.
2: { replace (n <=? 448) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
replace (n <=? 448) with false by (symmetry; apply Z.leb_gt; lia).
step. zstep. step. if_cases K3; zify_cond K3.
2: { replace (n <=? 3968) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
replace (n <=? 3968) with false by (symmetry; apply Z.leb_gt; lia).
step. zstep. step. if_cases K4; zify_cond K4.
2: { replace (n <=? 16128) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
replace (n <=? 16128) with false by (symmetry; apply Z.leb_gt; lia).
step. zstep. step. if_cases K5; zify_cond K5.
2: { replace (n <=? 32256) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
replace (n <=? 32256) with false by (symmetry; apply Z.leb_gt; lia).
step. zstep. zstep. zstep.
apply evtF_done. destruct (Z.leb_spec n 64512) as [K6|K6]; eexists.
- replace (n <? 64513) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
- replace (n <? 64513) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rz_clamp_spec : forall RNG ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (n rz : Z),
0 <= n < 2^40 -> 0 <= rz <= 7 ->
rng_aimg RNG ->
evtF bsegs RNG (fun ms' =>
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0) (Z_to_bv 64 (Z.max n 8)) (Z_to_bv 64 8) a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 rz) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x3253c) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0) (Z_to_bv 64 7) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 rz) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x32520) fc None m (seg_rom bsegs)).
Proof.
intros until rz. intros N RZ RIMG.
step. Local Ltac2 Set LiaHints.tbl := fun () => "00:0>10635129997.3920419410667.3920419410667.4045782037665.3945782037794.3846702646762.3861479276013.3961479276013.4061929812368.3961929812368.4000000700;00?00C00G00N00R00V00Y00\S2RZ2K1S2K2S2K2S2RZS2RZS2RZ2K0S2K2S2K2S1NS1N".
if_cases K0; zify_cond K0.
-
step. if_cases K1; zify_cond K1.
+ step. step. step. if_cases K2; zify_cond K2.
* replace (Z.max n 8) with n by lia. apply evtF_done. reflexivity.
* step. replace (Z.max n 8) with 8 by lia. apply evtF_done. reflexivity.
+ step. replace rz with 7 by lia. step. step. step. if_cases K2; zify_cond K2.
* step. replace (Z.max n 8) with 8 by lia. apply evtF_done. reflexivity.
* step. replace (Z.max n 8) with n by lia. apply evtF_done. reflexivity.
- step. replace rz with 0 by lia. step. if_lit. step. step. step. if_cases K2; zify_cond K2.
+ replace (Z.max n 8) with n by lia. apply evtF_done. reflexivity.
+ step. replace (Z.max n 8) with 8 by lia. apply evtF_done. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition allocA_cells (m : amem) (ctx t : Z) : Prop :=
rw_cells bsegs m AINITED [C1 (Z_to_bv 8 1)]
/\ rw_cells bsegs m ARSSLIM [C1 (Z_to_bv 8 0)]
/\ rw_cells bsegs m 0x9fcf8 [C8 (Z_to_bv 64 (2^40)); C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)]
/\ rw_cells bsegs m ATSDI [C1 (Z_to_bv 8 1)] /\ rw_cells bsegs m ATSDK [C4 (Z_to_bv 64 0)]
/\ rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] /\ rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)]
/\ rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)].
End CANSEC1.
