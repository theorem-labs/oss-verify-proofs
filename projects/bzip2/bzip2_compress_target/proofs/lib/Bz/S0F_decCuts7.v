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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDU6 BzDUM BzDU7 DecCutF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU6 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU7 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Export S0F_decRet.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzImg0TacF.
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition S0F_cut_L7T (A : act14) (F : nat) (t : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x26 x27 x28 x29 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f16 f32 f40 f56 f64 f72 f80 f88 f136 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 (Z_to_bv 64 (sv_nSelectors L)) f32 f40 (Z_to_bv 64 (sv_alphaSize L + 43888)) f56 f64 f72 f80 f88 (Z_to_bv 64 (sv_nGroups L))
         (Z_to_bv 64 ((a_S A) + 2124)) (Z_to_bv 64 ((a_S A) + 7884)) (Z_to_bv 64 ((a_S A) + 3152)) (Z_to_bv 64 ((a_S A) + 7820))
         f136 (Z_to_bv 64 ((a_S A) + 57820)) (Z_to_bv 64 ((a_S A) + 51628)) (Z_to_bv 64 ((a_S A) + 45436)) f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (a_usp A + -320) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    (dinv_L7T L d t /\ (t < sv_nGroups L)%Z) ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_L7T F L d s t))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 ((a_S A) + 64036)) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (a_S A)) (Z_to_bv 64 ((a_S A) + 43888)) (Z_to_bv 64 ((a_S A) + 64012)) (Z_to_bv 64 ((a_S A) + 2047)) x23 (Z_to_bv 64 t) (Z_to_bv 64 ((a_S A) + 43888 + 258 * t)) x26 x27 x28 x29 (Z_to_bv 64 (sv_alphaSize L)) x31)
          (a_F A) (Z_to_bv 64 0x1dd0c) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition S0F_cut_L7C (A : act14) (F : nat) (t mn mx : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x9 x10 x11 x12 x14 x16 x17 x23 x26 x27 x28 x29 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f16 f32 f40 f56 f64 f72 f80 f88 f136 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 (Z_to_bv 64 (sv_nSelectors L)) f32 f40 (Z_to_bv 64 (sv_alphaSize L + 43888)) f56 f64 f72 f80 f88 (Z_to_bv 64 (sv_nGroups L))
         (Z_to_bv 64 ((a_S A) + 2124)) (Z_to_bv 64 ((a_S A) + 7884)) (Z_to_bv 64 ((a_S A) + 3152)) (Z_to_bv 64 ((a_S A) + 7820))
         f136 (Z_to_bv 64 ((a_S A) + 57820)) (Z_to_bv 64 ((a_S A) + 51628)) (Z_to_bv 64 ((a_S A) + 45436)) f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (a_usp A + -320) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    dinv_L7C L d t mn mx ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_L7C F L d s t mn mx))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 ((a_S A) + 64036)) x9 x10 x11 x12 (Z_to_bv 64 (258 * t)) x14 (Z_to_bv 64 mx) x16 x17 (Z_to_bv 64 mn) (Z_to_bv 64 (a_S A)) (Z_to_bv 64 ((a_S A) + 43888)) (Z_to_bv 64 ((a_S A) + 64012)) (Z_to_bv 64 ((a_S A) + 2047)) x23 (Z_to_bv 64 t) (Z_to_bv 64 ((a_S A) + 43888 + 258 * t)) x26 x27 x28 x29 (Z_to_bv 64 (sv_alphaSize L)) x31)
          (a_F A) (Z_to_bv 64 0x1dd58) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition S0F_cut_L7D (A : act14) (F : nat) (t : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f16 f32 f40 f56 f64 f72 f80 f88 f136 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 (Z_to_bv 64 (sv_nSelectors L)) f32 f40 (Z_to_bv 64 (sv_alphaSize L + 43888)) f56 f64 f72 f80 f88 (Z_to_bv 64 (sv_nGroups L))
         (Z_to_bv 64 ((a_S A) + 2124)) (Z_to_bv 64 ((a_S A) + 7884)) (Z_to_bv 64 ((a_S A) + 3152)) (Z_to_bv 64 ((a_S A) + 7820))
         f136 (Z_to_bv 64 ((a_S A) + 57820)) (Z_to_bv 64 ((a_S A) + 51628)) (Z_to_bv 64 ((a_S A) + 45436)) f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (a_usp A + -320) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    dinv_L7T L d (t + 1) /\ (0 <= t < sv_nGroups L)%Z ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_L7T F L d s (t + 1)))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 ((a_S A) + 64036)) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (a_S A)) (Z_to_bv 64 ((a_S A) + 43888)) (Z_to_bv 64 ((a_S A) + 64012)) (Z_to_bv 64 ((a_S A) + 2047)) (Z_to_bv 64 (sv_alphaSize L)) (Z_to_bv 64 (t + 1)) (Z_to_bv 64 ((a_S A) + 43888 + 258 * t)) x26 x27 x28 x29 (Z_to_bv 64 (sv_alphaSize L)) x31)
          (a_F A) (Z_to_bv 64 0x1dda0) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition S0F_cut_H7M (A : act14) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x24 x25 x26 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f16 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 (Z_to_bv 64 (sv_nSelectors L)) f32 f40 f48 f56 f64 f72 f80 f88 f96
         (Z_to_bv 64 ((a_S A) + 2124)) (Z_to_bv 64 ((a_S A) + 7884)) (Z_to_bv 64 ((a_S A) + 3152)) (Z_to_bv 64 ((a_S A) + 7820))
         f136 f144 f152 f160 f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (a_usp A + -320) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    dinv_H7M L d ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_H7M F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 ((a_S A) + 64036)) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (a_S A)) x20 x21 (Z_to_bv 64 ((a_S A) + 2047)) (Z_to_bv 64 (sv_alphaSize L)) x24 x25 x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1dddc) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition S0F_cut_L7G (A : act14) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x24 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96
         (Z_to_bv 64 ((a_S A) + 2124)) (Z_to_bv 64 ((a_S A) + 7884)) (Z_to_bv 64 ((a_S A) + 3152)) (Z_to_bv 64 ((a_S A) + 7820))
         f136 f144 f152 f160 f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (a_usp A + -320) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    dinv_L7G L d ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_L7G F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -320)) (a_gp A) (a_tp A) x5 x6 (Z_to_bv 64 (100000 * d_bs100k d)) (Z_to_bv 64 ((a_S A) + 64036)) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (a_S A)) x20 x21 (Z_to_bv 64 ((a_S A) + 2047)) (Z_to_bv 64 (sv_alphaSize L)) x24 (Z_to_bv 64 (sv_nSelectors L)) (Z_to_bv 64 (sv_alphaSize L - 2)) x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1de7c) (a_fc A) None m (seg_rom s0segs)).

End ACeilS1.
