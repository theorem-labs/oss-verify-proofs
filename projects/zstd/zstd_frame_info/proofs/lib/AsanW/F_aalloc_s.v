(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg AProto ABase.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AKit.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
        F (Z_to_bv 64 0x36588) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> RIMG RSTK. atop_facts.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  Local Ltac2 Set LiaHints.tbl := fun () => "00@0>11805467289.5520433961190.4821212737002.6124972240369.6131399144472.4832600174396.5536789963889.613830427394.49 43061431595.4645221239098.5554164510851.5554164510851.5657293592682.6163235321900.5463235321900.5567081926311.5500000100200300400500900:00>00B00G00H00I00J00N00R00SSSSSSS2HBSS2LOS2LOS3SPRSSSS2LOS2LOS".
carve_frame 16%nat ST.
  do 2 step.                                   (* [comment removed for export] *)
  zstep. step. zstep. step. if_lit.           (* [comment removed for export] *)
  step. zstep. step. if_lit.                  (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                 (* [comment removed for export] *)
  zstep. step. step. step. zstep. zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
  lstep. zstep. step. step. if_lit.           (* [comment removed for export] *)
  step. zstep. step. if_lit.                  (* [comment removed for export] *)
  do 4 step.                                  (* [comment removed for export] *)
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
        F (Z_to_bv 64 0x36588) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> RIMG RSTK. atop_facts.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  Local Ltac2 Set LiaHints.tbl := fun () => "00@0>11805467289.5520433961190.4824972240369.6131399144472.4832394322977.6132600174396.553341391738.61 3830427394.49 43061431595.4645221239098.5554164510851.5554164510851.5657293592682.6163235321900.5463235321900.5567081926311.5500000100200300400500900:00>00B00G00H00I00J00N00R00SSSSSSS2HBSS2LOS2LOS3SPRSSSS2LOS2LOS".
carve_frame 16%nat ST.
  do 2 step.                                   (* [comment removed for export] *)
  zstep. step. zstep. step. if_lit.           (* [comment removed for export] *)
  step. zstep. step. if_lit.                  (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                 (* [comment removed for export] *)
  zstep. step. step. step. zstep. zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
  lstep. zstep. step. step. if_lit.           (* [comment removed for export] *)
  step. zstep. step. if_lit.                  (* [comment removed for export] *)
  do 4 step.                                  (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ARSSLIM : Z := 0x1230e2.
#[using="Type"] Lemma rss_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem),
  rw_cells asegs m ARSSLIM [C1 (Z_to_bv 8 0)] ->
  rng_aimg RNG ->
  evtF asegs RNG (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                      F (ret_pc ra) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5db44) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros C RIMG. unfold ARSSLIM in *.
  step. Local Ltac2 Set LiaHints.tbl := fun () => "0020>39213690267.3853510313878.44000001002SS".
lstep. zstep. step. apply evtF_done. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma can_poison_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem),
  rw_cells asegs m ACANPOISON [C1 (Z_to_bv 8 1)] ->
  rng_aimg RNG ->
  evtF asegs RNG (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                      F (ret_pc ra) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x52f5c) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros C RIMG. unfold ACANPOISON in *.
  step. Local Ltac2 Set LiaHints.tbl := fun () => "0030>52523015478.4453510313878.4465250765371.38000001002003SSS".
lstep. step. zstep. step. apply evtF_done. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ALSAN_TLSOFF : Z := 0x99a90.   (* [comment removed for export] *)
Definition ALSAN_CNT : Z := 0x5d3e20.       (* [comment removed for export] *)
#[using="Type"] Lemma lsan_disabled_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem),
  tp = Z_to_bv 64 ATP ->
  rw_cells asegs m ALSAN_TLSOFF [C8 (Z_to_bv 64 0x10)] ->                       (* [comment removed for export] *)
  rw_cells asegs m ALSAN_CNT [C4 (Z_to_bv 64 0)] ->
  rng_aimg RNG ->
  evtF asegs RNG (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                      F (ret_pc ra) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x7f150) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros -> C1 C2 RIMG. unfold ALSAN_TLSOFF, ALSAN_CNT, ATP in *.
  step. step. zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0020>53510313878.4461471995341.38000001002SS".
lstep. zstep. step. apply evtF_done. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AMHOOKS : Z := 0x132940.
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
        F (Z_to_bv 64 0x5fd60) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI HK RIMG RSTK. unfold AMHOOKS in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  Local Ltac2 Set LiaHints.tbl := fun () => "00U0>11805467289.5511805467289.5611805467289.5711805467289.5815685060272.5617221588796.5517776320428.5617776320429.5519006120615.5821296828022.5523230285244.5725435258127.5625435258127.5725566553219.5833680001082.5534290115814.4938785412078.5838806986883.5538806986883.5639939554818.5041564619544.4942831019478.5643061431595.4743987951407.5745221239098.5848468589166.575180980284.58 53767577772.5654618151079.5755104759171.57563227834.57  59178106163.566166287527.55 63235321901.5463235321901.5564666605650.5665309901038.5500000100200300400800<00@00D00E00F00J00K00L00M00R00S00\00]00^00b00c00h00l01001501>01B01F01G01H01M01N01O01S01W01`01iSSSSS2HBS2HBS2LOS2LOSSS2HBSSSS3SPRSS4CEIL2LOSSS2LOSS3SPRS2LOS2LOS3SPRS4CEIL2LOS2HBS2LOSSS3SPRSSS2LOS2LOS4CEIL2LOS4CEIL2LO".
carve_frame 32%nat ST.
  do 5 step.                                   (* [comment removed for export] *)
  do 2 step.                                   (* [comment removed for export] *)
  step. step.                                  (* [comment removed for export] *)
  step. zstep. step. step. if_lit.            (* [comment removed for export] *)
  do 6 step.                                   (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
(* [comment removed for export] *)
