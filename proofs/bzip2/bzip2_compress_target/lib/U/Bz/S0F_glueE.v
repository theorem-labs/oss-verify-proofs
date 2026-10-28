(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import GlueTac. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzInv BzTac S0_glueE.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLia.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac StoreFast.tlia ::= RelLia.tlia_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Lemma glueD0F : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b : bzs) (Q : machine_state -> Prop),
  rw_cells s0segs m (bv_unsigned sp + -128) (STRM_CELLS b) -> bzs_wf b -> mem_inv s0segs m ->
  (forall t0' a1', evt s0segs Q (atEnd 0x16024 sp gp tp t0' t1 t2 (Z_to_bv 64 (if (bs_av b =? 0)%Z then 1 else 0)) s1 a1' a2 a3 a4 a5 a6 a7
                                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)) ->
  evt s0segs Q (MS (mkR (Z_to_bv 64 0x15fe4) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 s0 s1
                      (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x15fe4) fc None m (seg_rom s0segs)).
Proof.
  intros until Q. intros STRM BWF MI HK. pose_word_ranges.
  cps_destruct BWF as (Q1 & Q2 & AI & AV & LEN & DLEN).
  (* [comment removed for export] *)
  step. btk. step. step. step. step.
  rewrite v_sltiu_b2z, (sx32_of_Z (bs_av b)), (unsigned_lit (bs_av b)) by lia.
  replace (Z.b2z (bs_av b <? bv_wrap 64 1)%Z) with (if (bs_av b =? 0)%Z then 1%Z else 0%Z)
    by (change (bv_wrap 64 1) with 1%Z; destruct (Z.eqb_spec (bs_av b) 0); destruct (Z.ltb_spec (bs_av b) 1); cbn; lia).
  enter_with HK. st_eq.
Qed.

(* [comment removed for export] *)
Definition glueTF_post (site : Z) (ra0 sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xs0 xs1 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra0) fc None m (seg_rom s0segs)
    /\ stk s0segs m lo (bv_unsigned sp)
    /\ (site = 0x1600c%Z -> a0 = Z_to_bv 64 0)
    /\ (site = 0x16034%Z -> a0 = xs1)
    /\ (site = 0x16024%Z -> xs0 = Z_to_bv 64 0 -> a0 = Z_to_bv 64 (-7))
    /\ (site = 0x16024%Z -> xs0 = Z_to_bv 64 1 -> a0 = Z_to_bv 64 (-8)).

Lemma glueTF : forall (site : Z) (sp gp tp t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (ra0 s0 s1 s2 s3 s4 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b : bzs) (lo : Z),
  (site = 0x1600c \/ site = 0x16024 \/ site = 0x16034)%Z ->
  (site = 0x16024%Z -> xs0 = Z_to_bv 64 0 \/ xs0 = Z_to_bv 64 1) ->
  rw_cells s0segs m (bv_unsigned sp + -128) (STRM_CELLS b) ->
  rw_cells s0segs m (bv_unsigned sp + -48) (SAVES s4 s3 s2 s1 s0 ra0) ->
  stk s0segs m lo (bv_unsigned sp + -128) -> (0x66000 <= lo)%Z -> (lo <= bv_unsigned sp - 128)%Z -> mem_inv s0segs m ->
  evt s0segs (glueTF_post site ra0 sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xs0 xs1 F fc m lo)
     (MS (mkR (Z_to_bv 64 site) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 xs0 xs1
              a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 site) fc None m (seg_rom s0segs)).
Proof.
  intros until lo. intros SITE X01 FRS FRV ST LOLO LO MI. pose_word_ranges. unfold SAVES in FRV.
  destruct SITE as [-> | [-> | ->]].
  - (* [comment removed for export] *) step. step.
    do 8 step. release_frame FRS ST (bv_unsigned sp + -48)%Z. release_frame FRV ST (bv_unsigned sp). step.
    unfold glueTF_post. finish. all: first [reflexivity | intros; try discriminate; try reflexivity; exfalso; lia].
  - (* [comment removed for export] *) destruct (X01 eq_refl) as [-> | ->]; step; step.
    all: do 8 step. all: release_frame FRS ST (bv_unsigned sp + -48)%Z. all: release_frame FRV ST (bv_unsigned sp). all: step.
    all: unfold glueTF_post; finish.
    all: first [reflexivity | intros; try discriminate; try reflexivity; try (exfalso; lia)].
    all: apply bv_eq; vm_compute; reflexivity.
  - (* [comment removed for export] *) step.
    do 8 step. release_frame FRS ST (bv_unsigned sp + -48)%Z. release_frame FRV ST (bv_unsigned sp). step.
    unfold glueTF_post. finish. all: first [reflexivity | intros; try discriminate; try reflexivity; exfalso; lia].
Qed.

End ACeilS1.
