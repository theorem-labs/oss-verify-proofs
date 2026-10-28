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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import GlueTac. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzInv BzTac.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
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
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section ACeilS1. Context {ACEIL__ : ACeil}.

Definition bzd_memexit_post (rc : Z) (ra0 sp gp tp t0 t1 t2 xs0 xs1 a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists (a1' a2' : word),
    ms' = MS (mkR ra0 sp gp tp t0 t1 t2 xs0 xs1 (Z_to_bv 64 rc) a1' a2' a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3 t4 t5 t6)
             F (ret_pc ra0) fc None m (seg_rom s0segs)
    /\ stk s0segs m lo (bv_unsigned sp).

Lemma bzd_memexit : forall (rc : Z) (rax spi sp gp tp t0 t1 t2 sv a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (x19 x24 : word)
    (ra0 xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 : word) (fj : list byte)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S lo : Z) (h : dsh),
  (rc = 0 \/ rc = -5 \/ rc = -3)%Z ->
  rw_cells s0segs m (bv_unsigned spi)
     [CB 8 fj; C8 xs11; C8 xs10; C8 xs9; C8 xs8; C8 xs7; C8 xs6; C8 xs5; C8 xs4; C8 xs3; C8 xs2; C8 xs1; C8 xs0; C8 ra0] ->
  stk s0segs m lo (bv_unsigned spi) -> (0x66000 <= lo)%Z -> (lo <= bv_unsigned spi)%Z -> (bv_unsigned spi + 112 <= 2 ^ 47)%Z ->
  Z_to_bv 64 (bv_unsigned spi + 112) = sp ->
  mem_inv s0segs m ->
  rw_cells s0segs m S (HEAD_CELLS h) -> (0 <= sh_state h < 2 ^ 31)%Z -> sh_state h <> 2%Z ->
  (0 < S)%Z -> (S + 64144 <= 2 ^ 47)%Z ->
  evt s0segs (bzd_memexit_post rc ra0 sp gp tp t0 t1 t2 xs0 xs1 a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3 t4 t5 t6 F fc m lo)
     (MS (mkR rax spi gp tp t0 t1 t2 (Z_to_bv 64 S) sv (Z_to_bv 64 rc) a1 a2 a3 a4 a5 a6 a7
              (Z_to_bv 64 (S + 1096)) x19 (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 1) (Z_to_bv 64 2) (Z_to_bv 64 (-1))
              x24 (Z_to_bv 64 100000) (Z_to_bv 64 (S + 64080)) (Z_to_bv 64 10) t3 t4 t5 t6)
         F (Z_to_bv 64 0x1481c) fc None m (seg_rom s0segs)).
Proof.
  intros until h. intros Hrc FR ST LOLO LO HI SPE MI HD Rst Nst S0 SHI. pose_word_ranges.
  (* [comment removed for export] *)
  destruct Hrc as [-> | [-> | ->]].
  all: step; step; step; btk; step; step; step; step; rewrite (sx32_of_Z (sh_state h)) by lia; btk;
       step; do 13 step; step; release_frame FR ST (bv_unsigned spi + 112)%Z;
       step; rewrite SPE; unfold bzd_memexit_post; finish; rewrite <- SPE, unsigned_lit by lia; assumption.
Qed.
End ACeilS1.
