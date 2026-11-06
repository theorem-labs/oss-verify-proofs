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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzInv BzTables BzContracts BzContracts0 DecCut S0_dec_U13 S0_decCuts BzLemmasT BzLemmasT2 BzWalkArith3.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Section ACeilS1. Context {ACEIL__ : ACeil}.


Section C.
  Variable A : act14.
  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).
  Notation Q := (POST14 DI_S0 A).

  Definition S0_cut_HFAST_ : Prop :=
    forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x24 x25 x26 x27 x29 x30 x31 : word)
           (nblock : Z) (sym unz : Z -> Z)
           (v : dv) (m : word -> option byte) (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m v ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96
         (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 7820))
         f136 f144 f152 f160 f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (usp + -320) ->
    munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpure cx (a_h0 A) (a_b0 A) (a_payload A) v ->
    (in_bits (dv_b v) (dv_h v) < in_bits (a_b0 A) (a_h0 A))%Z ->
    sh_state (dv_h v) = 2%Z -> sh_solen (dv_h v) = 0%Z ->
    eob_facts cx v nblock sym unz ->
    b_small cx = 0%Z ->
    (0 <= sh_origPtr (dv_h v) < nblock)%Z ->
    (forall j, 0 <= j <= 256 -> sv32 (dv_cf v) j = psum unz j)%Z ->
    evt s0segs Q
      (MS (mkR x1 (Z_to_bv 64 (usp + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 (S + 64036)) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 S) (Z_to_bv 64 (S + 3152)) x21 (Z_to_bv 64 (S + 1096)) x23 x24 x25 x26 x27 (Z_to_bv 64 nblock) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1e920) (a_fc A) None m (seg_rom s0segs)).

  Definition S0_cut_HSMALL_ : Prop :=
    forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x24 x25 x26 x27 x29 x30 x31 : word)
           (nblock : Z) (sym unz : Z -> Z)
           (v : dv) (m : word -> option byte) (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m v ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96
         (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 7820))
         f136 f144 f152 f160 f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (usp + -320) ->
    munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpure cx (a_h0 A) (a_b0 A) (a_payload A) v ->
    (in_bits (dv_b v) (dv_h v) < in_bits (a_b0 A) (a_h0 A))%Z ->
    sh_state (dv_h v) = 2%Z -> sh_solen (dv_h v) = 0%Z ->
    eob_facts cx v nblock sym unz ->
    b_small cx = 1%Z ->
    (0 <= sh_origPtr (dv_h v) < nblock)%Z ->
    (forall j, 0 <= j <= 256 -> sv32 (dv_cf v) j = psum unz j)%Z ->
    evt s0segs Q
      (MS (mkR x1 (Z_to_bv 64 (usp + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 (S + 64036)) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 S) (Z_to_bv 64 (S + 3152)) x21 (Z_to_bv 64 (S + 1096)) x23 x24 x25 x26 x27 (Z_to_bv 64 nblock) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1e6cc) (a_fc A) None m (seg_rom s0segs)).

  (* [comment removed for export] *)
  Section E.
  Variables (nblock : Z) (sym unz : Z -> Z).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  End E.

  (* [comment removed for export] *)
  Section F.
  Variables (nblock : Z) (sym unz tt0 : Z -> Z).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  End F.

  (* [comment removed for export] *)
  Section Sm.
  Variables (nblock : Z) (sym unz ll16_0 ll4_0 : Z -> Z).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  End Sm.
End C.
End ACeilS1.

Notation S0_cut_HFAST := S0_cut_HFAST_.
Notation S0_cut_HSMALL := S0_cut_HSMALL_.
