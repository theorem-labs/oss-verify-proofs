(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib Arr Frame SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts BzContracts0 BzLemmasMtf DecCut DecAux.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecAuxM DecTac DecTac2 DecTacM BzWalkArith3 S0_dec_U13 S0_decCuts.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0_decCuts7.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0_decCuts7.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDefs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzInv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzContracts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzContracts0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac.DecAuxB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAuxM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_dec_U13 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_decCuts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_decCuts7.S0_decCutsB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_decCuts7.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Musl Require Import S0_memset.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit DecFast DecFastT.
Local Ltac DecCut.revive H MUL WML AOK ::= DecFast.revive_cached H MUL WML AOK.
Local Ltac DecCut.dpure_from DP ::= DecFast.dpure_from_fast DP.
Local Ltac DecCut.open_dmem DM ::= DecFast.open_dmem_red DM.
Local Ltac DecTac.gb_next keep Wloc IB ::= DecFastT.gb_next_red keep Wloc IB.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import DecFastM.
Local Ltac DecTacM.revive_f H MUL WML AOK ::= DecFastM.revive_f_fast H MUL WML AOK.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLia RelLiaR.
Local Ltac lia ::= RelLia.lia_rf3.
Local Ltac StoreFast.tlia ::= RelLiaR.tlia_rr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Lemma addiw_m1 : forall x, (-1 <= x <= 2147483646)%Z ->
  bv_swrap 32 (Z.land x 18446744073709551615 + 1) = (x + 1)%Z.
Proof.
  intros x Hx. destruct (Z.eq_dec x (-1)) as [->|NE].
  - vm_compute. reflexivity.
  - rewrite (land64_small x) by lia. rewrite swrap32_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)

Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.
  Variables ng nsc alpha : Z.
  Hypothesis L7G : S0_cut_L7G A ng nsc alpha.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).
  Notation Q := (POST14 DI_S0 A).

  Ltac prep DM MU :=
    unfold W14, D14, DSTATE_SIZE in MU; cbn [app blk_ivls b_s b_strm] in MU; open_dmem DM; s2img.

  (* [comment removed for export] *)
  Notation KCOMMON m v K :=
    (dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m v ->
     stk s0segs m (a_lo A) (usp + -320) ->
     munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
     dpure cx (a_h0 A) (a_b0 A) (a_payload A) v ->
     (in_bits (dv_b v) (dv_h v) < in_bits (a_b0 A) (a_h0 A))%Z ->
     sh_state (dv_h v) <> 2%Z -> (1 <= sm_nInUse (dv_d v) <= 256)%Z ->
     (2 <= ng <= 6)%Z -> (1 <= nsc <= 18002)%Z ->
     selm_ok (r_sel (dv_r v)) nsc ng -> (sm_nInUse (dv_d v) + 2)%Z = alpha ->
     tabs_ok (dv_r v) ng alpha -> ag32s (r_unz (dv_r v)) (fun _ => 0%Z) 256 -> K) (only parsing).
  Notation KFR m j0 f8 f16 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 pb :=
    (S0FR A m j0 f8 f16 (Z_to_bv 64 nsc) f32 f40 f48 f56 f64 f72 f80 f88 f96
         (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 7820))
         f136 f144 f152 f160 f168 f176 f184 f192 f200 pb) (only parsing).

  (* [comment removed for export] *)
  Definition L7K (ii : Z) : Prop :=
    forall (x1 x5 x6 x9 x16 x18 x20 x21 x24 x27 x28 x29 x30 x31 : word)
           (v : dv) (m : word -> option byte)
           (j0 : list byte) (f8 f16 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    KFR m j0 f8 f16 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 pb ->
    KCOMMON m v (
    (0 <= ii <= 15)%Z ->
    (forall l, (ii < l <= 15)%Z -> sv32 (r_mtfb (dv_r v)) l = (3840 + 16 * l)%Z) ->
    evt s0segs Q
      (MS (mkR x1 (Z_to_bv 64 (usp + -320)) (a_gp A) (a_tp A) x5 x6 (Z_to_bv 64 (100000 * b_n cx)) (Z_to_bv 64 (S + 64036)) x9
              (Z_to_bv 64 (S + 3724)) (Z_to_bv 64 15) (Z_to_bv 64 (16 * ii + 15)) (Z_to_bv 64 (S + 7820)) (Z_to_bv 64 (3855 + 16 * ii))
              (Z_to_bv 64 (3855 + 16 * ii)) x16 (Z_to_bv 64 ii) x18 (Z_to_bv 64 S) x20 x21
              (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 alpha) x24 (Z_to_bv 64 nsc) (Z_to_bv 64 (alpha - 2)) x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1de34) (a_fc A) None m (seg_rom s0segs))).

  (* [comment removed for export] *)
  Definition L7J (ii d : Z) : Prop :=
    forall (x1 x9 x18 x20 x21 x24 x27 x28 x29 x30 x31 : word)
           (v : dv) (m : word -> option byte)
           (j0 : list byte) (f8 f16 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    KFR m j0 f8 f16 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 pb ->
    KCOMMON m v (
    (0 <= ii <= 15)%Z -> (0 <= d <= 15)%Z ->
    (forall l, (ii < l <= 15)%Z -> sv32 (r_mtfb (dv_r v)) l = (3840 + 16 * l)%Z) ->
    evt s0segs Q
      (MS (mkR x1 (Z_to_bv 64 (usp + -320)) (a_gp A) (a_tp A)
              (Z_to_bv 64 (S + 3724 + 3855 + 16 * ii - d)) (Z_to_bv 64 (16 * ii + 15 - d)) (Z_to_bv 64 (100000 * b_n cx))
              (Z_to_bv 64 (S + 64036)) x9
              (Z_to_bv 64 (S + 3724)) (Z_to_bv 64 15) (Z_to_bv 64 (16 * ii + 15)) (Z_to_bv 64 (S + 7820)) (Z_to_bv 64 (3855 + 16 * ii - d))
              (Z_to_bv 64 (3855 + 16 * ii)) (Z_to_bv 64 ii) (Z_to_bv 64 (d - 1)) x18 (Z_to_bv 64 S) x20 x21
              (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 alpha) x24 (Z_to_bv 64 nsc) (Z_to_bv 64 (alpha - 2)) x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1de44) (a_fc A) None m (seg_rom s0segs))).

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End R.

(* [comment removed for export] *)

End ACeilS1.
