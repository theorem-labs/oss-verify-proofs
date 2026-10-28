(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts BzContracts0 DecCut S0_dec_U13.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDU6. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU6 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Export S0F_decRet S0F_decCuts.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzImg0TacF.
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition S0F_cut_L6W (A : act14) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x5 x6 x7 x8 x10 x12 x13 x14 x15 x16 x17 x19 x21 x24 x25 x27 x28 x29 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f96 f104 f112 f120 f128 f136 f144 f160 f168 f176 f184 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 (a_S A + 2047)) f96 f104 f112 f120 f128 f136 f144 (Z_to_bv 64 (sv_t L)) f160 f168 f176 f184 f192 (Z_to_bv 64 (a_S A + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (a_usp A + -336) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    dinv_L6W L d ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_L6W F L d s))
      (MS (mkR (Z_to_bv 64 (sv_nGroups L)) (Z_to_bv 64 (a_usp A + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 (Z_to_bv 64 (sv_i L)) x10 (Z_to_bv 64 (sv_curr L)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (a_S A)) x19 (Z_to_bv 64 (a_S A + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) (Z_to_bv 64 (sv_alphaSize L)) x24 x25 (Z_to_bv 64 (sv_nSelectors L)) x27 x28 x29 (Z_to_bv 64 (a_S A + 7884)) x31)
          (a_F A) (Z_to_bv 64 0x26d74) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition S0F_cut_HHB (A : act14) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x24 x25 x27 x28 x29 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 (a_S A + 2047)) f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 (Z_to_bv 64 (a_S A + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (a_usp A + -336) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    dinv_HHB L d ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_HHB F L d s))
      (MS (mkR (Z_to_bv 64 (sv_nGroups L)) (Z_to_bv 64 (a_usp A + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (a_S A)) x19 (Z_to_bv 64 (a_S A + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) (Z_to_bv 64 (sv_alphaSize L)) x24 x25 (Z_to_bv 64 (sv_nSelectors L)) x27 x28 x29 (Z_to_bv 64 (a_S A + 7884)) x31)
          (a_F A) (Z_to_bv 64 0x268e4) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition S0F_cut_L6T (A : act14) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x19 x21 x24 x25 x27 x28 x29 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 (a_S A + 2047)) f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 (Z_to_bv 64 (a_S A + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (a_usp A + -336) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    dinv_HCOD L d ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_HCOD F L d s))
      (MS (mkR (Z_to_bv 64 (sv_nGroups L)) (Z_to_bv 64 (a_usp A + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 (Z_to_bv 64 (sv_t L)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (a_S A)) x19 (Z_to_bv 64 (a_S A + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) (Z_to_bv 64 (sv_alphaSize L)) x24 x25 (Z_to_bv 64 (sv_nSelectors L)) x27 x28 x29 (Z_to_bv 64 (a_S A + 7884)) x31)
          (a_F A) (Z_to_bv 64 0x26808) (a_fc A) None m (seg_rom s0segs)).


Lemma S0F_L6T_HCOD : forall A F, S0F_cut_L6T A F -> S0F_cut_HCOD A F.
Proof. intros A F H. unfold S0F_cut_HCOD. intros. eapply H; eassumption. Qed.

End ACeilS1.
