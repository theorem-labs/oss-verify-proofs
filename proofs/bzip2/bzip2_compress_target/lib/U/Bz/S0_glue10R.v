(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv DecCut S0_dec_U13. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import GlueTac. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import S0_glue10K.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLia.
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
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLiaA. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require RelLiaR.
Local Ltac lia ::= RelLiaA.lia_rf.
Local Ltac StoreFast.tlia ::= RelLiaR.tlia_rr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Notation FR10 mm usp j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 pb
              e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 era :=
  (rw_cells s0segs mm (usp + -336)
     [CB 8 j0; C8 f8; C8 f16; C8 f24; C8 f32; C8 f40; C8 f48; C8 f56; C8 f64; C8 f72; C8 f80; C8 f88; C8 f96;
      C8 f104; C8 f112; C8 f120; C8 f128; C8 f136; C8 f144; C8 f152; C8 f160; C8 f168; C8 f176; C8 f184; C8 f192; C8 f200;
      C8 f208; C8 f216;
      CB 8 pb; C8 e11; C8 e10; C8 e9; C8 e8; C8 e7; C8 e6; C8 e5; C8 e4; C8 e3; C8 e2; C8 e1; C8 e0; C8 era]) (only parsing).
Section ACeilS1. Context {ACEIL__ : ACeil}.


Section R.
  Variables (usp S lo : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Hypothesis GEO : (0 < S /\ S + 64144 <= lo /\ alloc_ceiling <= lo /\ lo <= usp - 1024 /\ usp < 2 ^ 64)%Z.

  (* [comment removed for export] *)
  Definition RK (Q : machine_state -> Prop) (m : word -> option byte) (r nblock : Z)
      (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 f160 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 era : word) : Prop :=
    forall (m' : word -> option byte) (y12 y13 y14 : word) (j1 j2 : list byte),
      rw_cells s0segs m' (S + 64036) (SAVE_CELLS j1 nblock j2) -> length j1 = 44%nat -> length j2 = 60%nat ->
      stk s0segs m' lo usp ->
      munch [(S + 64036, S + 64144)]%Z m m' -> wmono s0segs m m' -> mem_inv s0segs m' ->
      evt s0segs Q
        (MS (mkR era (Z_to_bv 64 usp) gp tp x5 x6 x7 e0 e1 (Z_to_bv 64 r) f160 y12 y13 y14 x15 x16 x17
                e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 x28 x29 x30 x31)
            F (ret_pc era) fc None m' (seg_rom s0segs)).

  (* [comment removed for export] *)
  Lemma g10_Rc : forall (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (r nblock snb0 : Z) (m : word -> option byte) (j1 j2 : list byte)
      (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 : word) (pb : list byte)
      (e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 era : word) (Q : machine_state -> Prop),
    FR10 m usp j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 pb
         e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 era ->
    rw_cells s0segs m (S + 64036) (SAVE_CELLS j1 snb0 j2) -> length j1 = 44%nat -> length j2 = 60%nat ->
    stk s0segs m lo (usp + -336) -> mem_inv s0segs m ->
    (0 <= nblock < 2 ^ 31)%Z ->
    RK Q m r nblock x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 f160 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 era ->
    evt s0segs Q
      (MS (mkR x1 (Z_to_bv 64 (usp + -336)) gp tp x5 x6 x7 x8 x9
              (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21
              (Z_to_bv 64 nblock) x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x2614c) fc None m (seg_rom s0segs)).
  Proof.
    intros until Q. intros FR SAV L1 L2 ST MI NB HK. unfold RK in HK.
    cps_pose GEO as (G1 & G2 & G3 & G4 & G5).
    pose proof (munch_refl [(S + 64036, S + 64144)]%Z m) as MU. pose proof (wmono_refl s0segs m) as WM.
    do 35 wstep.
    (* [comment removed for export] *)
    apply (rw_cells_merge_firstn s0segs _ _ _ 11) in SAV. cbn [firstn skipn cells_size csize cells_bytes cbytes Nat.add app] in SAV.
    apply (rw_cells_merge_mid s0segs _ _ _ 2 12) in SAV. cbn [firstn skipn cells_size csize cells_bytes cbytes Nat.add app] in SAV.
    do 15 wstep.
    release_frame FR ST usp.
    enter_with HK; [ st_eq | exact SAV | | | exact ST | exact MU | exact WM | ];
      [ cbn [cells_bytes cbytes app]; rewrite ?length_app, ?length_le4; reflexivity
      | cbn [cells_bytes cbytes app]; rewrite ?length_app, ?length_le4, ?length_le8; reflexivity
      | match goal with H : mem_inv s0segs _ |- _ => exact H end ].
  Qed.

  (* [comment removed for export] *)
  Lemma g10_R : forall (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (r nblock snb0 : Z) (m : word -> option byte) (j1 j2 : list byte)
      (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 : word) (pb : list byte)
      (e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 era : word) (Q : machine_state -> Prop),
    FR10 m usp j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 pb
         e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 era ->
    rw_cells s0segs m (S + 64036) (SAVE_CELLS j1 snb0 j2) -> length j1 = 44%nat -> length j2 = 60%nat ->
    stk s0segs m lo (usp + -336) -> mem_inv s0segs m ->
    (0 <= nblock < 2 ^ 31)%Z ->
    RK Q m r nblock x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 f160 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 era ->
    evt s0segs Q
      (MS (mkR x1 (Z_to_bv 64 (usp + -336)) gp tp x5 x6 x7 x8 x9
              (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21
              (Z_to_bv 64 nblock) x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x2613c) fc None m (seg_rom s0segs)).
  Proof.
    intros until Q. intros FR SAV L1 L2 ST MI NB HK.
    cps_pose GEO as (G1 & G2 & G3 & G4 & G5).
    wstep. wstep. wstep. wstep.
    enter_with g10_Rc; [ st_eq | exact FR | exact SAV | exact L1 | exact L2 | exact ST | exact MI | exact NB | exact HK ].
  Qed.
End R.

End ACeilS1.
