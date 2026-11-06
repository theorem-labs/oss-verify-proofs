(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Tac ImageA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Str_tac Startup_glue.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout R_small R_m2s R_thread I_consts I_qck X_atexit D_kit I_ikit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require I_vprintfw.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require F_fwritex.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_small.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_m2s.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_thread.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_consts.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_qck.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.X_atexit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_ikit.TwinB__.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_vprintfw.TwinB__.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Definition fpfr (usp : Z) (junk : list byte) (ra s0 s1 s2 : word) : list cell :=
  [CB 8 junk; C8 (Z_to_bv 64 (usp + -48)); C8 (Z_to_bv 64 (usp + -48)); C8 (Z_to_bv 64 (usp + -48)); C8 s2; C8 s1; C8 s0; C8 ra].

Definition fpwA1_post (usp : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 a3 a4 a5 a6 a7 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (t0 t1 t2 a3' a4' a5' a6' a7' t3 t4 t5 t6 : word) (junk : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x46abc) (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 a1 a0 (Z_to_bv 64 0x1eb96) a1
                  (Z_to_bv 64 (usp + -48)) a3' a4' a5' a6' a7' (Z_to_bv 64 (usp + -48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x45ba8) fc None m' (seg_rom bsegs)
    /\ munch [(usp - 128, usp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp + -112)
    /\ rw_cells bsegs m' (usp + -112) (fpfr usp junk ra s0 s1 s2)
    /\ rw_cells bsegs m' (usp + -48) [C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7].

Lemma fprintf_walkA1 : forall (usp lo : Z)
    ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 128 -> 0x62b000 <= lo -> usp <= 2^47 -> pfcells m -> mem_inv bsegs m ->
  evt bsegs (fpwA1_post usp ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 a3 a4 a5 a6 a7 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4325c) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO LOLO SPH PFC MI.
  pose proof (munch_refl [(usp - 128, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU112 : bv_unsigned (Z_to_bv 64 (usp + -112)) = usp + -112) by (apply unsigned_lit; lia).
  destruct PFC as (AI & GCF & CPF & RVP & RVF).
  carve_frame 112%nat ST. rename FR into FRp.
  apply (rw_cells_split_CB bsegs _ _ [] 112 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRp; [| reflexivity].
  cbn [mk_CB_cells app] in FRp.
  xsteps_to 0x5a460%Z.
  call try_init_spec; [exact AI | rewrite EU112; exact ST | rewrite EU112; lia | lia | assumption |].
  rename POST into ST.
  xsteps_to 0x5a460%Z.
  call try_init_spec; [exact AI | exact ST | rewrite EU112; lia | lia | assumption |].
  rename POST into ST. rewrite EU112 in ST.
  xsteps_to 0x45ba8%Z.
  apply (proj1 (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_fwritex.TwinB__.rw_cells_app bsegs _ _ [_; _; _; _; _; _; _; _] _)) in FRp. destruct FRp as [FRp1 FRva].
  cbn [cells_size csize Nat.add] in FRva. replace (usp + -112 + Z.of_nat 64) with (usp + -48) in FRva by lia.
  apply evt_done. unfold fpwA1_post. do 14 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FRp1| exact FRva].
Qed.

(* [comment removed for export] *)
Lemma fprintf_walkA2 : forall (usp : Z) (junk : list byte) (ra0 c0 c1 c2 : word)
    ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  rw_cells bsegs m (usp + -112) (fpfr usp junk ra0 c0 c1 c2) -> ro_cells bsegs m 0xceba8 [C8 (Z_to_bv 64 0xc29a0)] ->
  usp <= 2^47 -> 112 <= usp -> mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (a3' : word), ms' =
      MS (mkR (Z_to_bv 64 0x46afc) (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 s0 s1 s1 s0 (Z_to_bv 64 (usp + -48)) a3' a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0xc29a0) fc None m (seg_rom bsegs))
    (MS (mkR ra (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x46abc) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros FRp1 RVF SPH SPL MI. unfold fpfr in FRp1.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU112 : bv_unsigned (Z_to_bv 64 (usp + -112)) = usp + -112) by (apply unsigned_lit; lia).
  do 8 lstep.
  apply evt_done. eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fprintf_walkB : forall (usp lo : Z) (junk : list byte) (a2 a3 a4 a5 a6 a7 : word)
    (ra' ra gp tp t0 t1 t2 s0 s1 s0' s1' a0 a1 a2' a3' a4' a5' a6' a7' s2 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  stk bsegs m lo (usp + -112) -> lo <= usp + -112 -> usp <= 2^47 ->
  rw_cells bsegs m (usp + -112) (fpfr usp junk ra s0 s1 s2) ->
  rw_cells bsegs m (usp + -48) [C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => (exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
                 ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m (seg_rom bsegs))
                 /\ stk bsegs m lo usp)
    (MS (mkR ra' (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 s0' s1' a0 a1 a2' a3' a4' a5' a6' a7' s2' s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x46afc) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO UT FRp1 FRva MI. unfold fpfr in FRp1.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU112 : bv_unsigned (Z_to_bv 64 (usp + -112)) = usp + -112) by (apply unsigned_lit; lia).
  do 6 lstep.
  release_frame FRp1 ST (usp + -48).
  release_frame FRva ST usp.
  apply evt_done. split; [| exact ST]. do 14 eexists. first [reflexivity | f_equal; f_equal; apply Z_to_bv_eqm; lia].
Qed.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow R_small R_m2s R_thread I_consts I_qck X_atexit D_kit I_ikit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import I_vprintfw.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require F_fwritex.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Definition fpfr (usp : Z) (junk : list byte) (ra s0 s1 s2 : word) : list cell :=
  [CB 8 junk; C8 (Z_to_bv 64 (usp + -48)); C8 (Z_to_bv 64 (usp + -48)); C8 (Z_to_bv 64 (usp + -48)); C8 s2; C8 s1; C8 s0; C8 ra].

Definition fpwA1_post (usp : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 a3 a4 a5 a6 a7 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (t0 t1 t2 a3' a4' a5' a6' a7' t3 t4 t5 t6 : word) (junk : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x46bd4) (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 a1 a0 (Z_to_bv 64 0x1eb96) a1
                  (Z_to_bv 64 (usp + -48)) a3' a4' a5' a6' a7' (Z_to_bv 64 (usp + -48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x45cc0) fc None m' (seg_rom asegs)
    /\ munch [(usp - 128, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -112)
    /\ rw_cells asegs m' (usp + -112) (fpfr usp junk ra s0 s1 s2)
    /\ rw_cells asegs m' (usp + -48) [C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7].

Lemma fprintf_walkA1 : forall (usp lo : Z)
    ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 128 -> 0x61e000 <= lo -> usp <= 2^47 -> pfcells m -> mem_inv asegs m ->
  evt asegs (fpwA1_post usp ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 a3 a4 a5 a6 a7 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x43374) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO LOLO SPH PFC MI.
  pose proof (munch_refl [(usp - 128, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU112 : bv_unsigned (Z_to_bv 64 (usp + -112)) = usp + -112) by (apply unsigned_lit; lia).
  destruct PFC as (AI & GCF & CPF & RVP & RVF).
  carve_frame 112%nat ST. rename FR into FRp.
  apply (rw_cells_split_CB asegs _ _ [] 112 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRp; [| reflexivity].
  cbn [mk_CB_cells app] in FRp.
  xsteps_to 0x5aa14%Z.
  call try_init_spec; [exact AI | rewrite EU112; exact ST | rewrite EU112; lia | lia | assumption |].
  rename POST into ST.
  xsteps_to 0x5aa14%Z.
  call try_init_spec; [exact AI | exact ST | rewrite EU112; lia | lia | assumption |].
  rename POST into ST. rewrite EU112 in ST.
  xsteps_to 0x45cc0%Z.
  apply (proj1 (F_fwritex.rw_cells_app asegs _ _ [_; _; _; _; _; _; _; _] _)) in FRp. destruct FRp as [FRp1 FRva].
  cbn [cells_size csize Nat.add] in FRva. replace (usp + -112 + Z.of_nat 64) with (usp + -48) in FRva by lia.
  apply evt_done. unfold fpwA1_post. do 14 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FRp1| exact FRva].
Qed.

(* [comment removed for export] *)
Lemma fprintf_walkA2 : forall (usp : Z) (junk : list byte) (ra0 c0 c1 c2 : word)
    ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  rw_cells asegs m (usp + -112) (fpfr usp junk ra0 c0 c1 c2) -> ro_cells asegs m 0xc17c8 [C8 (Z_to_bv 64 0xb55c0)] ->
  usp <= 2^47 -> 112 <= usp -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a3' : word), ms' =
      MS (mkR (Z_to_bv 64 0x46c14) (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 s0 s1 s1 s0 (Z_to_bv 64 (usp + -48)) a3' a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0xb55c0) fc None m (seg_rom asegs))
    (MS (mkR ra (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x46bd4) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros FRp1 RVF SPH SPL MI. unfold fpfr in FRp1.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU112 : bv_unsigned (Z_to_bv 64 (usp + -112)) = usp + -112) by (apply unsigned_lit; lia).
  do 8 lstep.
  apply evt_done. eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fprintf_walkB : forall (usp lo : Z) (junk : list byte) (a2 a3 a4 a5 a6 a7 : word)
    (ra' ra gp tp t0 t1 t2 s0 s1 s0' s1' a0 a1 a2' a3' a4' a5' a6' a7' s2 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  stk asegs m lo (usp + -112) -> lo <= usp + -112 -> usp <= 2^47 ->
  rw_cells asegs m (usp + -112) (fpfr usp junk ra s0 s1 s2) ->
  rw_cells asegs m (usp + -48) [C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] ->
  mem_inv asegs m ->
  evt asegs (fun ms' => (exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
                 ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m (seg_rom asegs))
                 /\ stk asegs m lo usp)
    (MS (mkR ra' (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 s0' s1' a0 a1 a2' a3' a4' a5' a6' a7' s2' s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x46c14) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO UT FRp1 FRva MI. unfold fpfr in FRp1.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU112 : bv_unsigned (Z_to_bv 64 (usp + -112)) = usp + -112) by (apply unsigned_lit; lia).
  do 6 lstep.
  release_frame FRp1 ST (usp + -48).
  release_frame FRva ST usp.
  apply evt_done. split; [| exact ST]. do 14 eexists. first [reflexivity | f_equal; f_equal; apply Z_to_bv_eqm; lia].
Qed.
