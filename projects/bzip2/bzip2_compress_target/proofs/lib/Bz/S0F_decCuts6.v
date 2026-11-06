(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzInv BzTables BzContracts BzContracts0 DecCut S0_dec_U13.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDU6 DecCutF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU6 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Export S0F_decRet S0F_decCuts.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzImg0TacF.
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition S0F_cut_L6W (A : act14) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x5 x6 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x24 x29 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96
         (Z_to_bv 64 ((a_S A) + 2124)) (Z_to_bv 64 ((a_S A) + 7884)) (Z_to_bv 64 ((a_S A) + 3152)) (Z_to_bv 64 ((a_S A) + 7820))
         f136 f144 f152 f160 f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (a_usp A + -320) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    dinv_L6W L d ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_L6W F L d s))
      (MS (mkR (Z_to_bv 64 (sv_nGroups L)) (Z_to_bv 64 (a_usp A + -320)) (a_gp A) (a_tp A) x5 x6 (Z_to_bv 64 (sv_t L)) (Z_to_bv 64 ((a_S A) + 64036)) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (sv_nSelectors L)) x21 (Z_to_bv 64 ((a_S A) + 2047)) x23 x24 (Z_to_bv 64 (sv_nSelectors L)) (Z_to_bv 64 (sv_i L)) (Z_to_bv 64 (sv_curr L)) (Z_to_bv 64 (sv_nblock L)) x29 (Z_to_bv 64 (sv_alphaSize L)) x31)
          (a_F A) (Z_to_bv 64 0x1e104) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition S0F_cut_HHB (A : act14) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x24 x25 x26 x27 x29 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96
         (Z_to_bv 64 ((a_S A) + 2124)) (Z_to_bv 64 ((a_S A) + 7884)) (Z_to_bv 64 ((a_S A) + 3152)) (Z_to_bv 64 ((a_S A) + 7820))
         f136 f144 f152 f160 f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (a_usp A + -320) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    dinv_HHB L d ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_HHB F L d s))
      (MS (mkR (Z_to_bv 64 (sv_nGroups L)) (Z_to_bv 64 (a_usp A + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 ((a_S A) + 64036)) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (sv_nSelectors L)) x21 (Z_to_bv 64 ((a_S A) + 2047)) x23 x24 x25 x26 x27 (Z_to_bv 64 (sv_nblock L)) x29 (Z_to_bv 64 (sv_alphaSize L)) x31)
          (a_F A) (Z_to_bv 64 0x1dc88) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition S0F_cut_L6T (A : act14) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x5 x6 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x24 x25 x26 x27 x29 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96
         (Z_to_bv 64 (a_S A + 2124)) (Z_to_bv 64 (a_S A + 7884)) (Z_to_bv 64 (a_S A + 3152)) (Z_to_bv 64 (a_S A + 7820))
         f136 f144 f152 f160 f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (a_usp A + -320) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    dinv_HCOD L d ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_HCOD F L d s))
      (MS (mkR (Z_to_bv 64 (sv_nGroups L)) (Z_to_bv 64 (a_usp A + -320)) (a_gp A) (a_tp A) x5 x6 (Z_to_bv 64 (sv_t L)) (Z_to_bv 64 (a_S A + 64036)) x9
              x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (sv_nSelectors L)) x21
              (Z_to_bv 64 (a_S A + 2047)) x23 x24 x25 x26 x27 (Z_to_bv 64 (sv_nblock L)) x29
              (Z_to_bv 64 (sv_alphaSize L)) x31)
          (a_F A) (Z_to_bv 64 0x1dbdc) (a_fc A) None m (seg_rom s0segs)).


Lemma S0F_L6T_HCOD : forall A F, S0F_cut_L6T A F -> S0F_cut_HCOD A F.
Proof. intros A F H. unfold S0F_cut_HCOD. intros. eapply H; eassumption. Qed.

End ACeilS1.
