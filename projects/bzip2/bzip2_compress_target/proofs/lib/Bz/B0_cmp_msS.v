(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCState BzCSortM BzArrD CmpMem CmpCut CmpFsKit0 BzCQsortM1 BzCQsortM2 BzCSewA AsanKit AsanCut AsanCutB0 AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasMs BzCLemmasMs2 BzCLemmasMs3 CmpCutMS CmpMsKit CmpMsKit2.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsV B0_cmp_fsS B0_cmp_msV.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition shc3 (b : byte) : list cell :=
  Eval cbv [repeat app] in (repeat (C1 b) 50 ++ repeat (C1 f2b) 8 ++ repeat (C1 b) 50 ++ repeat (C1 f2b) 8 ++ repeat (C1 b) 50).

Lemma shc3_size : forall b, cells_size (shc3 b) = 166%nat.
Proof. intros b. reflexivity. Qed.
Lemma shc3_bytes : forall b, cells_bytes (shc3 b) = repeat b 50 ++ (repeat f2b 8 ++ (repeat b 50 ++ (repeat f2b 8 ++ repeat b 50))).
Proof. intros b. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ams_stack_readers : forall (X : msenv) (Y : amenv) (SHF : Z) (W : list (Z * Z)) (m0 : word -> option byte),
  msenv_ok X -> amenv_ok X Y -> sanchor (am_FB Y) SHF -> app_fp W ->
  rw_cells b0segs m0 (SHF + 4) (shc3 z8) ->
  shzW b0segs W m0 (am_SLO Y) (am_SLO Y + 400) /\ shzW b0segs W m0 (am_SHI Y) (am_SHI Y + 400) /\ shzW b0segs W m0 (am_SD Y) (am_SD Y + 400).
Proof.
  intros X Y SHF W m0 XOK YOK AX AF [[Hwf Hb] _].
  pose proof alloc_ceiling_lt47 as C47.
  msenv_open XOK. amenv_open YOK.
  rewrite shc3_bytes in Hb. apply bytes_at_app in Hb. destruct Hb as [Hlo Hb]. apply bytes_at_app in Hb. destruct Hb as [_ Hb].
  apply bytes_at_app in Hb. destruct Hb as [Hhi Hb]. apply bytes_at_app in Hb. destruct Hb as [_ Hd].
  rewrite !repeat_length in Hhi, Hd.
  assert (M8 : forall o, (o mod 8 = 0 -> (am_FB Y + o) mod 8 = 0)%Z).
  { intros o Ho. destruct AX as [M8 _]. rewrite <- Z.add_mod_idemp_l by lia. rewrite M8. exact Ho. }
  assert (Elo : shad (am_SLO Y) = (SHF + 4)%Z).
  { unfold shad, SHB. rewrite YSLO. exact (sanchor_addr_lit _ _ 32 4 AX eq_refl). }
  assert (Ehi : shad (am_SHI Y) = (SHF + 4 + Z.of_nat 50 + Z.of_nat 8)%Z).
  { unfold shad, SHB. rewrite YSHI. rewrite (sanchor_addr_lit _ _ 496 62 AX eq_refl). lia. }
  assert (Ed : shad (am_SD Y) = (SHF + 4 + Z.of_nat 50 + Z.of_nat 8 + Z.of_nat 50 + Z.of_nat 8)%Z).
  { unfold shad, SHB. rewrite YSD. rewrite (sanchor_addr_lit _ _ 960 120 AX eq_refl). lia. }
  split; [| split].
  - refine (proj1 (sh_of_ushadow b0segs W m0 (am_SLO Y) 400 _ ltac:(rewrite YSLO; apply M8; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) AF)).
    rewrite Elo. exact Hlo.
  - refine (proj1 (sh_of_ushadow b0segs W m0 (am_SHI Y) 400 _ ltac:(rewrite YSHI; apply M8; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) AF)).
    rewrite Ehi. exact Hhi.
  - refine (proj1 (sh_of_ushadow b0segs W m0 (am_SD Y) 400 _ ltac:(rewrite YSD; apply M8; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) AF)).
    rewrite Ed. exact Hd.
Qed.

(* [comment removed for export] *)
Lemma shc3_transport : forall W (m m' : word -> option byte) A b,
  id (rw_cells b0segs m A (shc3 b)) -> munch W m m' -> wmono b0segs m m' -> disjoint_from W A 166 -> id (rw_cells b0segs m' A (shc3 b)).
Proof.
  unfold id. intros W m m' A b H MU WM D. apply (rw_cells_transport b0segs W m m' A (shc3 b) H MU WM).
  rewrite shc3_size. exact D.
Qed.

Section B0MS.
  Variable X : msenv. Variable Y : amenv. Variable SHF : Z. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis YOK : amenv_ok X Y.
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation WSH := [(SHF + 4, SHF + 170)]%Z.

  Ltac sb0 := wstep; change (le1 (Z_to_bv 64 0)) with [z8]; mem_after_store.
  Ltac sbf8 := wstep; change (le1 (Z_to_bv 64 (-8))) with [f8b]; mem_after_store.

  (* [comment removed for export] *)
  Lemma B0_ms_scope_begin : forall (me m : word -> option byte) (b : byte)
      (ra sp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells b0segs m (SHF + 4) (shc3 b) -> mem_inv b0segs m -> munch WSH me m -> wmono b0segs me m ->
    (forall m', rw_cells b0segs m' (SHF + 4) (shc3 z8) -> mem_inv b0segs m' -> munch WSH me m' -> wmono b0segs me m' ->
       evt b0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 SHF) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0xa2448) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 SHF) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa21f0) fc None m (seg_rom b0segs)).
  Proof.
    intros me m b ra sp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SH MI MU WMo K.
    unfold shc3 in SH.
    do 150 sb0.
    apply K; [unfold shc3; exact SH| exact MI| exact MU| exact WMo].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_ms_scope_end : forall (me m : word -> option byte) (b : byte)
      (ra sp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells b0segs m (SHF + 4) (shc3 b) -> mem_inv b0segs m -> munch WSH me m -> wmono b0segs me m ->
    (forall m', rw_cells b0segs m' (SHF + 4) (shc3 f8b) -> mem_inv b0segs m' -> munch WSH me m' -> wmono b0segs me m' ->
       evt b0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 SHF) (Z_to_bv 64 (-8)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0xa3bd0) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 SHF) (Z_to_bv 64 (-8)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa3978) fc None m (seg_rom b0segs)).
  Proof.
    intros me m b ra sp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SH MI MU WMo K.
    unfold shc3 in SH.
    do 150 sbf8.
    apply K; [unfold shc3; exact SH| exact MI| exact MU| exact WMo].
  Qed.

End B0MS.

End ACeilS1.
