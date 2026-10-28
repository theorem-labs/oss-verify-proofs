(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts BzContracts0 DecCut S0_dec_U13.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF S0F_decRet.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import DecFast.
Local Ltac DecCut.revive H MUL WML AOK ::= DecFast.revive_cached H MUL WML AOK.
Local Ltac DecCut.dpure_from DP ::= DecFast.dpure_from_fast DP.
Local Ltac DecCut.open_dmem DM ::= DecFast.open_dmem_red DM.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzImg0TacF.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require NormFast. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require FLiaA.
Local Ltac lia ::= FLiaA.lia_f.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require GbKit GbKitF.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import U0_decKit.
Section ACeilS1. Context {ACEIL__ : ACeil}.

Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).
  Notation W := (W14 DI_S0 (a_cx A) (bv_unsigned (a_sp A))).

  (* [comment removed for export] *)
  Ltac mkR_setf_args n x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    lazymatch n with
    | 1%Z => constr:(fun wq : word => mkR wq x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 2%Z => constr:(fun wq : word => mkR x1 wq x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 3%Z => constr:(fun wq : word => mkR x1 x2 wq x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 4%Z => constr:(fun wq : word => mkR x1 x2 x3 wq x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 5%Z => constr:(fun wq : word => mkR x1 x2 x3 x4 wq x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 6%Z => constr:(fun wq : word => mkR x1 x2 x3 x4 x5 wq x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 7%Z => constr:(fun wq : word => mkR x1 x2 x3 x4 x5 x6 wq x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 8%Z => constr:(fun wq : word => mkR x1 x2 x3 x4 x5 x6 x7 wq x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 9%Z => constr:(fun wq : word => mkR x1 x2 x3 x4 x5 x6 x7 x8 wq x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 10%Z => constr:(fun wq : word => mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 wq x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 11%Z => constr:(fun wq : word => mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 wq x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 12%Z => constr:(fun wq : word => mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 wq x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 13%Z => constr:(fun wq : word => mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 wq x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 14%Z => constr:(fun wq : word => mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 wq x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 15%Z => constr:(fun wq : word => mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 wq x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 16%Z => constr:(fun wq : word => mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 wq x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 17%Z => constr:(fun wq : word => mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 wq x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 18%Z => constr:(fun wq : word => mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 wq x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 19%Z => constr:(fun wq : word => mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 wq x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 20%Z => constr:(fun wq : word => mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 wq x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 21%Z => constr:(fun wq : word => mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 wq x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 22%Z => constr:(fun wq : word => mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 wq x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | 23%Z => constr:(fun wq : word => mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 wq x24 x25 x26 x27 x28 x29 x30 x31)
    | 24%Z => constr:(fun wq : word => mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 wq x25 x26 x27 x28 x29 x30 x31)
    | 25%Z => constr:(fun wq : word => mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 wq x26 x27 x28 x29 x30 x31)
    | 26%Z => constr:(fun wq : word => mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 wq x27 x28 x29 x30 x31)
    | 27%Z => constr:(fun wq : word => mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 wq x28 x29 x30 x31)
    | 28%Z => constr:(fun wq : word => mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 wq x29 x30 x31)
    | 29%Z => constr:(fun wq : word => mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 wq x30 x31)
    | 30%Z => constr:(fun wq : word => mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 wq x31)
    | 31%Z => constr:(fun wq : word => mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 wq)
    end.
  Ltac mkR_setf R n :=
    lazymatch R with
    | mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31 => mkR_setf_args n x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    | TNode (TNode (TNode (TNode (TNode (TNode TEmpty (Some ?x31) TEmpty) (Some ?x15) TEmpty) (Some ?x7) (TNode TEmpty (Some ?x23) TEmpty)) (Some ?x3) (TNode (TNode TEmpty (Some ?x19) TEmpty) (Some ?x11) (TNode TEmpty (Some ?x27) TEmpty))) (Some ?x1) (TNode (TNode (TNode TEmpty (Some ?x17) TEmpty) (Some ?x9) (TNode TEmpty (Some ?x25) TEmpty)) (Some ?x5) (TNode (TNode TEmpty (Some ?x21) TEmpty) (Some ?x13) (TNode TEmpty (Some ?x29) TEmpty)))) None (TNode (TNode (TNode (TNode TEmpty (Some ?x16) TEmpty) (Some ?x8) (TNode TEmpty (Some ?x24) TEmpty)) (Some ?x4) (TNode (TNode TEmpty (Some ?x20) TEmpty) (Some ?x12) (TNode TEmpty (Some ?x28) TEmpty))) (Some ?x2) (TNode (TNode (TNode TEmpty (Some ?x18) TEmpty) (Some ?x10) (TNode TEmpty (Some ?x26) TEmpty)) (Some ?x6) (TNode (TNode TEmpty (Some ?x22) TEmpty) (Some ?x14) (TNode TEmpty (Some ?x30) TEmpty)))) => mkR_setf_args n x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    end.

  (* [comment removed for export] *)
  Ltac til_join rq skip HD STRM ST MU WM MI MUL WML :=
    lazymatch goal with |- evt ?sg ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
    lazymatch type of HD with rw_cells _ _ ?Sa ?csH =>
    lazymatch type of STRM with rw_cells _ _ ?strm (?c0 :: ?c1 :: ?c2 :: C4 ?tih0 :: ?rest) =>
    lazymatch type of ST with stk _ _ ?lo ?base =>
    lazymatch type of MU with munch ?W ?ma _ =>
    lazymatch type of MUL with munch ?WL ?m0 _ =>
    let Rf := mkR_setf R rq in
    let J := constr:(forall (wq tq : word) (m2 : word -> option byte),
               rw_cells sg m2 Sa csH -> rw_cells sg m2 strm (c0 :: c1 :: c2 :: C4 tq :: rest) ->
               stk sg m2 lo base -> munch W ma m2 -> wmono sg ma m2 -> mem_inv sg m2 ->
               munch WL m0 m2 -> wmono sg m0 m2 ->
               evt sg Q (MS (Rf wq) F (Z_to_bv 64 skip) fc rv m2 ro)) in
    let JN := fresh "JN" in
    enough J as JN;
    [ | clear HD STRM ST MU WM MI MUL WML; try clear m;
        intros ?wq ?tq ?m HD STRM ST MU WM MI MUL WML; cbv beta ]
    end end end end end end.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac til_use JN :=
    eapply JN;
    [ match goal with H : rw_cells _ _ (b_s _) _ |- _ => exact H end
    | match goal with H : rw_cells _ _ (b_strm _) _ |- _ => exact H end
    | match goal with H : stk _ _ _ _ |- _ => exact H end
    | match goal with H : munch _ (a_m0 _) _ |- _ => exact H end
    | match goal with H : wmono _ (a_m0 _) _ |- _ => exact H end
    | match goal with H : mem_inv _ _ |- _ => exact H end
    | match goal with H : munch _ _ _ |- munch ?W _ _ => match type of H with munch W _ _ => exact H end end
    | match goal with H : wmono _ ?a _ |- wmono _ ?a _ => exact H end ].
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac gbF_close DP MUL WML :=
    lazymatch goal with DM0 : dmem _ _ _ _ _ _ _ |- dmem _ ?cx _ _ _ ?mm _ =>
      eapply (GbKitF.gbF_dmem_close _ _ AOK _ (GbKit.di_in_img_ok DI_S0 eq_refl) _ _ _ _ _ _ _ _ DM0 DP MUL WML);
      [ dvF_cbn; dmodel_cbn; match goal with H : rw_cells _ mm (b_s cx) _ |- _ => exact_cells H end
      | dvF_cbn; dmodel_cbn; match goal with H : rw_cells _ mm (b_strm cx) _ |- _ => exact_cells H end
      | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity ]
    end.
  Ltac cut_sideG MUL WML DP :=
    lazymatch goal with
    | |- dmem _ _ _ _ _ _ _ => first [ gbF_close DP MUL WML | revive_all MUL WML AOK; cut_sideF DP ]
    | |- rw_cells _ _ (bv_unsigned (a_sp _) + _)%Z _ =>      (* [comment removed for export] *)
        first [ cut_sideF DP
              | match goal with H : hidden (rw_cells _ _ (bv_unsigned (a_sp _) + _)%Z _) |- _ => revive H MUL WML AOK end; cut_sideF DP
              | revive_all MUL WML AOK; cut_sideF DP ]
    | |- _ => cut_sideF DP
    end.
  Ltac gbF_exit HK HD STRM MUL WML DP MD FU breg n :=
    lazymatch type of HD with rw_cells _ _ _ ?cs =>
      let c := eval cbv beta iota zeta delta [cell_at csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add] in (cell_at cs 32%nat) in
      lazymatch c with Some (C4 (Z_to_bv 64 ?bbx)) =>
        let w := fresh "wb" in gbword breg w bbx;
        [ first [ apply sx32_mod32; lia | apply pullw_reg32; lia ]
        | erewrite (drun_bits' _ _ _ _ _ _ _ n) in MD by first [reflexivity | cbn; lia];
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          eapply evt_eq; [ | eapply (HK _ _ _ _ _ _ _ mm _ MD) ]; only 1: unify_memF;
          [ | eapply fuel_ok_gbst_bits; [exact FU | cbn; lia] | try cut_sideG MUL WML DP .. ];
          [ dvF_cbn; dmodel_cbn; st_eq | try (cbn [length]; unset_Z; lia) .. ] end ]
      end end.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac gbF_ret HRET MUL WML DP MD NB n :=
    erewrite (drun_eof' _ _ _ _ _ _ _ n) in MD by first [reflexivity | cbn; lia];
    rewrite MD;
    (eapply evt_eq; [ | eapply (HRET _ _ _ (JK _ _ _ _ _ _ _ _ _ _ _ _ _ _)) ]; only 1: unify_memF; try cut_sideG MUL WML DP; only 1: (dvF_cbn; dmodel_cbn; st_eq)); [exact NB | apply dpost14_ne; dmodel_cbn; cbv; discriminate].

  (* [comment removed for export] *)
  Lemma S0F_gb_1d940 : forall (Q : dres -> machine_state -> Prop), S0F_RET_OK A Q -> S0F_RET A Q ->
    forall (F : nat) (L : dsv) (d : dst) (s : dstrm) (J : jk)
           (x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte)
           (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 pb ->
    stk s0segs m (a_lo A) (usp + -336) ->
    munch W (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    (0 <= sv_nblock L <= 900000)%Z ->
    fuel_ok F d s ->
    (forall (F1 : nat) (bb' bl' : Z) (inp' : list Z) (tin' : Z) (til' tih' : word) (m' : word -> option byte) (wb : word),
       let d2 := gbst d 32 bb' bl' in
       let s1 := DSTRM inp' (s_out s) (s_avail_out s) tin' (s_tout s) in
       drun F 32 L d s = dgo F1 (gb_after 32 (gbval bb' bl' 1) L (d_set_bsLive d2 (bl' - 1)) s1) ->
       fuel_ok F1 (d_set_bsLive d2 (bl' - 1)) s1 -> (F1 < F)%nat ->
       dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m' (dvF cx (jk_set_t J til' tih') d2 s1) ->
       S0FR A m' j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 pb ->
       stk s0segs m' (a_lo A) (usp + -336) ->
       munch W (a_m0 A) m' -> wmono s0segs (a_m0 A) m' -> mem_inv s0segs m' ->
       dpureF cx (a_b0 A) (a_payload A) (jk_set_t J til' tih') d2 s1 ->
       (0 <= bb' < 2^32)%Z -> (1 <= bl' <= 32)%Z -> (bv_unsigned wb mod 4294967296 = bb')%Z ->
       (8 * Z.of_nat (length inp') + bl' = 8 * Z.of_nat (length (s_in s)) + d_bsLive d)%Z ->
       forall (y5 y6 y15 y16 y17 : word),
       evt s0segs (Q (drun F 32 L d s))
         (MS (mkR x1 (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) y5 y6 x7 x8 x9 (Z_to_bv 64 (bl' - 1)) (Z_to_bv 64 32) (Z_to_bv 64 (-1)) (Z_to_bv 64 (-8)) wb y15 y16 y17
                 (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
             (a_F A) (Z_to_bv 64 0x26690) (a_fc A) None m' (seg_rom s0segs))) ->
    evt s0segs (Q (drun F 32 L d s))
      (MS (mkR x1 (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 (Z_to_bv 64 (d_bsLive d)) (Z_to_bv 64 32) (Z_to_bv 64 (-1)) (Z_to_bv 64 (-8)) x14 x15 x16 x17
                 (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x265ec) (a_fc A) None m (seg_rom s0segs)).
  Proof.
    intros Q HRET HRETR. intros until pb. intros DM FR ST MU WM MI DP NB FU HK.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold W14, D14, DSTATE_SIZE in MU. cbn [app blk_ivls b_s b_strm] in MU.
    destruct s as [inp sout sav stin stout]. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    pose proof DM as DM0. open_dmemF DM. s2img. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    destruct (fuel_ok_pos _ _ _ (proj1 (dpureF_bl _ _ _ _ _ _ DP)) FU) as [f EF]. subst F.
    pose proof (drun_gbst f 32 L d (DSTRM inp sout sav stin stout)) as MD. apply (fuel_ok_gbst _ _ 32) in FU.
    pose proof (dpureF_in _ _ _ _ _ _ DP) as IR.
    set (bl := d_bsLive d) in *. set (bb := d_bsBuff d) in *.
    hide_all_but (HD, STRM).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl [(S, S + 68); (b_strm cx, b_strm cx + 20)]%Z mm) as MUL;
      pose proof (wmono_refl s0segs mm) as WML end.
    wstepl.
    wstepl. if_cases K; zify_cond_z K.
    { (* [comment removed for export] *)
      wstepl. notrap. wstepl. wstepl.
      gbF_exit HK HD STRM MUL WML DP MD FU 14%Z 1%Z.
    }
    { (* [comment removed for export] *)
      wstepl. wstepl. wstepl. wstepl. wstepl.
      rewrite (strm_flag_ok cx (proj1 AOK)).
      wstepl. notrap.
      wstepl.
      wstepl. if_cases K2; zify_cond K2.
      { (* [comment removed for export] *)
        assert (AI1 : (1 <= Z.of_nat (length inp))%Z) by (lin_unbox LIN; clear - K2 LIN; zb_masks; mlia). clear K2. destruct inp as [|bz inp1]; [exfalso; cbn in AI1; lia|]. destruct (in_rel_head (a_payload A) _ _ _ IR eq_refl) as [b8 [NTH Ebz]]. cbn [s_in length] in NTH. cbn [length] in *. rewrite Nat2Z.inj_succ in *. subst bz.
        wstepl. wstepl. notrap.
        wstepl.
        pose proof PAY as PAYL. revive PAYL MUL WML AOK.
        pose proof (u8ro_read s0segs _ (b_src cx) (a_payload A) (b_len cx - Z.succ (Z.of_nat (length inp1)))%Z b8 _ PAYL ltac:(rewrite <- NTH; f_equal; lia) ltac:(lia) eq_refl) as RD.
        (let pv := reg_val 17%Z in lazymatch pv with Z_to_bv 64 ?e => replace e with (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z by lia end).
        wstepl. clear RD PAYL.
        wstepl. wstepl. wstepl. wstepl. wstepl.
        wstepl. notrap.
        wstepl. forget_reg 5%Z wtil.
        wstepl. wstepl. wstepl. forget_reg 5%Z wtil2. wstepl. wstepl. wstepl.
        (* [comment removed for export] *)
        cell_mod32 HD 32%nat. change (2^32)%Z with 4294967296%Z in HD. rewrite (pullw_mod32 bb b8) in HD by lia.
        set (bb1 := u32 (Z.lor (Z.shiftl bb 8) (bv_unsigned b8))) in *.
        pose proof (u32_range' (Z.lor (Z.shiftl bb 8) (bv_unsigned b8))) as Rbb1. change (u32 _) with bb1 in Rbb1.
        replace (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))) + 1)%Z with (b_src cx + (b_len cx - Z.of_nat (length inp1)))%Z in STRM by lia.
        replace (Z.succ (Z.of_nat (length inp1)) + -1)%Z with (Z.of_nat (length inp1)) in STRM by lia.
        erewrite (drun_pull_D _ _ _ _ _ _ 1%Z) in MD by first [reflexivity | cbn; lia]. change (u32 _) with bb1 in MD.
        apply (fuel_ok_pull_D _ _ _ _ _ bb1 _ _ _ _ _ (stin + 1)) in FU.
        destruct (fuel_ok_gbst_S _ _ _ _ _ _ FU ltac:(lia)) as [f1 Ef1]. subst f.
        pose proof (in_rel_tail _ _ (DSTRM inp1 sout sav (stin + 1) stout) _ _ IR eq_refl eq_refl) as IR1.
        til_join 16%Z 0x26678%Z HD STRM ST MU WM MI MUL WML.
        { wstepl; if_cases K3; [ til_use JN | wstepl; wstepl; wstepl; til_use JN ]. }
        wstepl. wstepl. if_false_z.
        wstepl. notrap. wstepl. wstepl.
        gbF_exit HK HD STRM MUL WML DP MD FU 14%Z 1%Z.
      }
      { (* [comment removed for export] *)
        assert (inp = []) as -> by (lin_unbox LIN; destruct inp; [reflexivity| exfalso; cbn [length] in K2, LIN; rewrite Nat2Z.inj_succ in K2, LIN; clear -K2 LIN; zb_masks; mlia]). clear K2.
        wstepl.
        gbF_ret HRET MUL WML DP MD NB 1%Z.
      }
    }
  Qed.

End R.

End ACeilS1.
