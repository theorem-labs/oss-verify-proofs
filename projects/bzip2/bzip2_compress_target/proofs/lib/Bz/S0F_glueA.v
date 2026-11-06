(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.bzip2.bzip2_compress_target.images Require Import Plain.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require GlueTac GlueCarve.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require GlueTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ACeilLia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLiaA RelLiaR.
Module S0_glueA.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.bzip2.bzip2_compress_target.images.Plain.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.GlueTac.
 Unset Lia Cache.
Import ListNotations.
Local Open Scope bv_scope.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeil OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.RunW.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeilLia.
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)

Local Ltac lia ::= RelLiaA.lia_rf.
Local Ltac StoreFast.tlia ::= RelLiaR.tlia_rr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
Definition glueA_post (ra0 sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 a3 a4 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 xa3 xa4 xa5 a6 a7 t3 t4 t5 t6 m2w : word) (m' : word -> option byte) (j56 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x144ac) (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0 t1 t2
                 (Z_to_bv 64 0) a4
                 (Z_to_bv 64 64144) (Z_to_bv 64 64144) (Z_to_bv 64 1) xa3 xa4 xa5 a6 a7
                 (Z_to_bv 64 (bv_unsigned sp + -128)) a0 a2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1fa40) fc None m' (seg_rom s0segs)
    /\ munch [(bv_unsigned sp + -160, bv_unsigned sp)]%Z m m' /\ wmono s0segs m m' /\ mem_inv s0segs m'
    /\ rw_cells s0segs m' (bv_unsigned sp + -128)
         [CB 56 j56; C8 (Z_to_bv 64 0x13dfc); C8 (Z_to_bv 64 0x13e04); C8 (Z_to_bv 64 0);
          C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra0]
    /\ rw_cells s0segs m' (bv_unsigned sp + -160) [C8 a3; C8 m2w; C8 a1; C8 (Z_to_bv 64 0x15710)]
    /\ stk s0segs m' lo (bv_unsigned sp + -160).

(* [comment removed for export] *)

End ACeilS1.
End S0_glueA.


From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require GlueCarve.
Module S0_glueB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.bzip2.bzip2_compress_target.images.Plain.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.GlueTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.GlueCarve.
 Unset Lia Cache.
Import ListNotations.
Local Open Scope bv_scope.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeil OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.RunW.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeilLia.
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)

Local Ltac lia ::= RelLiaA.lia_rf.
Local Ltac StoreFast.tlia ::= RelLiaR.tlia_rr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition glueB0_post (ra0 sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-3)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra0) fc None m (seg_rom s0segs)
    /\ stk s0segs m lo (bv_unsigned sp).

Lemma glueB0 : forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (ra0 xs0 xs1 xs2 xs3 xs4 fa fb m2w : word) (j56 : list byte)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  rw_cells s0segs m (bv_unsigned sp + -128)
     [CB 56 j56; C8 (Z_to_bv 64 0x13dfc); C8 (Z_to_bv 64 0x13e04); C8 (Z_to_bv 64 0); C8 xs4; C8 xs3; C8 xs2; C8 xs1; C8 xs0; C8 ra0] ->
  rw_cells s0segs m (bv_unsigned sp + -160) [C8 fa; C8 m2w; C8 fb; C8 (Z_to_bv 64 0x15710)] ->
  stk s0segs m lo (bv_unsigned sp + -160) -> (0x5c000 <= lo)%Z -> (lo <= bv_unsigned sp - 160)%Z ->
  mem_inv s0segs m ->
  evt s0segs (glueB0_post ra0 sp gp tp xs0 xs1 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 F fc m lo)
      (MS (mkR (Z_to_bv 64 0x144ac) (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0 t1 t2 (Z_to_bv 64 0) s1
              (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (bv_unsigned sp + -128)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x144ac) fc None m (seg_rom s0segs)).
Proof.
  intros until lo. intros FR FR0 ST LOLO LO MI.
  pose_word_ranges.
  (* [comment removed for export] *)
  step. btk. step. do 6 step.
  release_frame FR0 ST (bv_unsigned sp + -128)%Z.
  (* [comment removed for export] *)
  step. step. bnt. step. do 6 step. step.
  release_frame FR ST (bv_unsigned sp).
  step.
  unfold glueB0_post. finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition glueB1_W (usp r : Z) : list (Z * Z) := [(usp + -160, usp); (r, r + 68); (r + 3152, r + 3196)]%Z.

(* [comment removed for export] *)

(* [comment removed for export] *)

End ACeilS1.
End S0_glueB.

Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.GlueTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.GlueCarve OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_glueA.S0_glueA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_glueA.S0_glueB.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLia.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLia.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac StoreFast.tlia ::= RelLia.tlia_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


Lemma glueAF : forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo dst dl src len small : Z),
  a0 = Z_to_bv 64 dst -> a1 = Z_to_bv 64 dl -> a2 = Z_to_bv 64 src -> a3 = Z_to_bv 64 len ->
  a4 = Z_to_bv 64 small -> a5 = Z_to_bv 64 0 ->
  (0 < dst < 2 ^ 64)%Z -> (0 < dl < 2 ^ 64)%Z -> (0 < src < 2 ^ 64)%Z -> (0 <= len < 2 ^ 27)%Z -> (0 <= small <= 1)%Z ->
  stk s0segs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 160)%Z -> (0x5c000 <= lo)%Z ->
  mem_inv s0segs m ->
  evt s0segs (glueA_post ra0 sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 a3 a4 F fc m lo)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x156a8) fc None m (seg_rom s0segs)).
Proof.
  intros until small. intros A0 A1 A2 A3 A4 A5 Hdst Hdl Hsrc Hlen Hsmall ST LO LOLO MI.
  pose proof (munch_refl [(bv_unsigned sp + -160, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl s0segs m) as WM.
  pose_word_ranges. subst a0 a1 a2 a3 a4 a5.
  carve_frame 128%nat ST.
  (* [comment removed for export] *)
  do 7 lstep.
  (* [comment removed for export] *)
  lstep. step. bnt. step. step. bnt. step. step. bnt.
  (* [comment removed for export] *)
  step. step. step. bnt. step. step. bnt. step.
  (* [comment removed for export] *)
  lstep. lstep. lstep.
  (* [comment removed for export] *)
  step. step. step. step.
  (* [comment removed for export] *)
  carve_frame 32%nat ST.
  do 5 lstep.
  (* [comment removed for export] *)
  step. step. step. step. step. bnt. step. bnt.
  (* [comment removed for export] *)
  step. step. step. bnt.
  (* [comment removed for export] *)
  step. step. bnt. step. step. lstep.
  (* [comment removed for export] *)
  step. step. bnt. step. step. lstep.
  (* [comment removed for export] *)
  step. step. step. step. step.
  (* [comment removed for export] *)
  step. step.
  unfold glueA_post. finish; [exact FR | exact FR0].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition glueA0_post (ra0 sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra0) fc None m' (seg_rom s0segs)
    /\ a0 = Z_to_bv 64 (-2)
    /\ munch [(bv_unsigned sp + -128, bv_unsigned sp)]%Z m m' /\ wmono s0segs m m' /\ mem_inv s0segs m'
    /\ stk s0segs m' lo (bv_unsigned sp).

Lemma glueA0 : forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  a0 = Z_to_bv 64 0 ->
  stk s0segs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 160)%Z -> (0x5c000 <= lo)%Z ->
  mem_inv s0segs m ->
  evt s0segs (glueA0_post ra0 sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x156a8) fc None m (seg_rom s0segs)).
Proof.
  intros until lo. intros A0 ST LO LOLO MI.
  pose proof (munch_refl [(bv_unsigned sp + -128, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl s0segs m) as WM.
  pose_word_ranges. subst a0.
  carve_frame 128%nat ST.
  (* [comment removed for export] *)
  do 7 lstep.
  (* [comment removed for export] *)
  lstep. step. btk.
  (* [comment removed for export] *)
  step. do 6 step. step.
  release_frame FR ST (bv_unsigned sp).
  step.
  unfold glueA0_post. finish. all: reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition glueB1F_post (ra0 sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (r dst dl dn src len small : Z)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 xs1 : word) (m' : word -> option byte) (q1 q2 p20 p4 p3 p12 q12 q4 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x15758) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 dl) xs1
                 (Z_to_bv 64 (bv_unsigned sp + -128)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1455c) fc None m' (seg_rom s0segs)
    /\ munch (glueB1_W (bv_unsigned sp) r) m m' /\ wmono s0segs m m' /\ mem_inv s0segs m'
    /\ rw_cells s0segs m' (bv_unsigned sp + -128)
         [C8 (Z_to_bv 64 src); C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 q1;
          C8 (Z_to_bv 64 dst); C4 (Z_to_bv 64 dn); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 q2;
          C8 (Z_to_bv 64 r); C8 (Z_to_bv 64 0x13dfc); C8 (Z_to_bv 64 0x13e04); C8 (Z_to_bv 64 0);
          C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra0]
    /\ rw_cells s0segs m' r (dhead_init (bv_unsigned sp + -128) small p20 p4 p3 p12)
    /\ rw_cells s0segs m' (r + 3152) (dmid_init q12 q4)
    /\ stk s0segs m' lo (bv_unsigned sp + -128).

Lemma glueB1F : forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (ra0 xs0 xs1 xs2 xs3 xs4 m2w : word) (j56 jh jm : list byte)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo r dst dl dn src len small : Z),
  rw_cells s0segs m (bv_unsigned sp + -128)
     [CB 56 j56; C8 (Z_to_bv 64 0x13dfc); C8 (Z_to_bv 64 0x13e04); C8 (Z_to_bv 64 0); C8 xs4; C8 xs3; C8 xs2; C8 xs1; C8 xs0; C8 ra0] ->
  rw_cells s0segs m (bv_unsigned sp + -160) [C8 (Z_to_bv 64 len); C8 m2w; C8 (Z_to_bv 64 dl); C8 (Z_to_bv 64 0x15710)] ->
  stk s0segs m lo (bv_unsigned sp + -160) -> (0x5c000 <= lo)%Z -> (lo <= bv_unsigned sp - 160)%Z ->
  mem_inv s0segs m ->
  s1 = Z_to_bv 64 small -> (0 <= small <= 1)%Z ->
  rw_cells s0segs m r [CB 68 jh] -> rw_cells s0segs m (r + 3152) [CB 44 jm] -> (0 < r)%Z -> (r + 64144 <= lo)%Z ->
  rw_cells s0segs m dl [C4 (Z_to_bv 64 dn)] -> (0 <= dn < 2 ^ 27)%Z -> (0 <= len < 2 ^ 27)%Z ->
  (bv_unsigned sp <= dl)%Z -> (dl + 4 <= 2 ^ 64)%Z ->
  (0 < dst < 2 ^ 64)%Z -> (0 < src < 2 ^ 64)%Z ->
  evt s0segs (glueB1F_post ra0 sp gp tp xs0 xs1 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 r dst dl dn src len small F fc m lo)
      (MS (mkR (Z_to_bv 64 0x144ac) (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0 t1 t2 (Z_to_bv 64 0) s1
              (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (bv_unsigned sp + -128)) (Z_to_bv 64 dst) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x144ac) fc None m (seg_rom s0segs)).
Proof.
  intros until small. intros FR FR0 ST LOLO LO MI S1 Hsmall BH BM R0 RHI DL DN LEN DLLO DLHI DST SRC.
  pose proof (munch_refl (glueB1_W (bv_unsigned sp) r) m) as MU. unfold glueB1_W in MU.
  pose proof (wmono_refl s0segs m) as WM.
  pose_word_ranges. subst s1.
  (* [comment removed for export] *)
  step. bnt. step. step. lstep. step.
  (* [comment removed for export] *)
  lstep. lstep. lstep.
  (* [comment removed for export] *)
  lstep. lstep. lstep. lstep.
  (* [comment removed for export] *)
  step. lstep. lstep. lstep. lstep.
  (* [comment removed for export] *)
  lstep. lstep. lstep. step.
  (* [comment removed for export] *)
  do 6 step.
  release_frame FR0 ST (bv_unsigned sp + -128)%Z.
  (* [comment removed for export] *)
  step. step. btk.
  (* [comment removed for export] *)
  step. rewrite (sx32_small (Z_to_bv 64 dn)) by (rewrite unsigned_lit by lia; lia).
  lstep. lstep. lstep. lstep. step. step.
  unfold glueB1F_post, dhead_init, dmid_init. finish; [exact FR | exact BH | exact BM].
Qed.

End ACeilS1.
