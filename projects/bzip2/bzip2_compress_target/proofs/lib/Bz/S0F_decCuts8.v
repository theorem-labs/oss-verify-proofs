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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU8 DecCutF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU8 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Export S0F_decRet S0F_decCutsM.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzImg0TacF.
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition S0F_cut_L8A (A : act14) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x7 x10 x12 x13 x14 x15 x16 x17 x21 x23 x24 x26 x27 x29 x30 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f184 f200 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96
         (Z_to_bv 64 ((a_S A) + 2124)) (Z_to_bv 64 ((a_S A) + 7884)) (Z_to_bv 64 ((a_S A) + 3152)) (Z_to_bv 64 ((a_S A) + 7820))
         (Z_to_bv 64 (sv_gSel L)) (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 (sv_groupNo L))
         (Z_to_bv 64 ((a_S A) + 57820 + 1032 * sv_gSel L)) (Z_to_bv 64 ((a_S A) + 51628 + 1032 * sv_gSel L)) f184 (Z_to_bv 64 (sv_gMinlen L)) f200 pb ->
    stk s0segs m (a_lo A) (a_usp A + -320) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    dinv_L8 1 L d ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_L8 F 1 L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -320)) (a_gp A) (a_tp A) x5 (Z_to_bv 64 ((a_S A) + 45436 + 1032 * sv_gSel L)) x7 (Z_to_bv 64 ((a_S A) + 64036)) (Z_to_bv 64 (sv_zn L)) x10 (Z_to_bv 64 (d_bsLive d)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sv_groupPos L)) (Z_to_bv 64 (a_S A)) (Z_to_bv 64 ((a_S A) + 3152)) x21 (Z_to_bv 64 ((a_S A) + 2047)) x23 x24 (Z_to_bv 64 (sv_nSelectors L)) x26 x27 (Z_to_bv 64 (sv_nblock L)) x29 x30 (Z_to_bv 64 (sv_zvec L)))
          (a_F A) (Z_to_bv 64 0x1d4d4) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition S0F_cut_L8G (A : act14) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x24 x26 x27 x29 x30 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f200 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96
         (Z_to_bv 64 ((a_S A) + 2124)) (Z_to_bv 64 ((a_S A) + 7884)) (Z_to_bv 64 ((a_S A) + 3152)) (Z_to_bv 64 ((a_S A) + 7820))
         (Z_to_bv 64 (sv_gSel L)) (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 (sv_groupNo L))
         (Z_to_bv 64 ((a_S A) + 57820 + 1032 * sv_gSel L)) (Z_to_bv 64 ((a_S A) + 51628 + 1032 * sv_gSel L)) (Z_to_bv 64 (sv_N L)) (Z_to_bv 64 (sv_gMinlen L)) f200 pb ->
    stk s0segs m (a_lo A) (a_usp A + -320) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    dinv_L8G L d ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_L8G F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -320)) (a_gp A) (a_tp A) x5 (Z_to_bv 64 ((a_S A) + 45436 + 1032 * sv_gSel L)) x7 (Z_to_bv 64 ((a_S A) + 64036)) (Z_to_bv 64 (sv_zn L)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sv_groupPos L)) (Z_to_bv 64 (a_S A)) x20 x21 (Z_to_bv 64 ((a_S A) + 2047)) (Z_to_bv 64 (sv_es L)) x24 (Z_to_bv 64 (sv_nSelectors L)) x26 x27 (Z_to_bv 64 (sv_nblock L)) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1ec68) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition S0F_cut_L8D (A : act14) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x7 x10 x12 x13 x14 x15 x16 x17 x21 x24 x26 x27 x29 x30 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f200 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96
         (Z_to_bv 64 ((a_S A) + 2124)) (Z_to_bv 64 ((a_S A) + 7884)) (Z_to_bv 64 ((a_S A) + 3152)) (Z_to_bv 64 ((a_S A) + 7820))
         (Z_to_bv 64 (sv_gSel L)) (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 (sv_groupNo L))
         (Z_to_bv 64 ((a_S A) + 57820 + 1032 * sv_gSel L)) (Z_to_bv 64 ((a_S A) + 51628 + 1032 * sv_gSel L)) (Z_to_bv 64 (sv_N L)) (Z_to_bv 64 (sv_gMinlen L)) f200 pb ->
    stk s0segs m (a_lo A) (a_usp A + -320) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    dinv_L8 3 L d ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_L8 F 3 L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -320)) (a_gp A) (a_tp A) x5 (Z_to_bv 64 ((a_S A) + 45436 + 1032 * sv_gSel L)) x7 (Z_to_bv 64 ((a_S A) + 64036)) (Z_to_bv 64 (sv_zn L)) x10 (Z_to_bv 64 (d_bsLive d)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sv_groupPos L)) (Z_to_bv 64 (a_S A)) (Z_to_bv 64 ((a_S A) + 3152)) x21 (Z_to_bv 64 ((a_S A) + 2047)) (Z_to_bv 64 (sv_es L)) x24 (Z_to_bv 64 (sv_nSelectors L)) x26 x27 (Z_to_bv 64 (sv_nblock L)) x29 x30 (Z_to_bv 64 (sv_zvec L)))
          (a_F A) (Z_to_bv 64 0x1ed0c) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition S0F_cut_L8CG (A : act14) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x23 x24 x26 x27 x29 x30 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f184 f200 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96
         (Z_to_bv 64 ((a_S A) + 2124)) (Z_to_bv 64 ((a_S A) + 7884)) (Z_to_bv 64 ((a_S A) + 3152)) (Z_to_bv 64 ((a_S A) + 7820))
         (Z_to_bv 64 (sv_gSel L)) (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 (sv_groupNo L))
         (Z_to_bv 64 ((a_S A) + 57820 + 1032 * sv_gSel L)) (Z_to_bv 64 ((a_S A) + 51628 + 1032 * sv_gSel L)) f184 (Z_to_bv 64 (sv_gMinlen L)) f200 pb ->
    stk s0segs m (a_lo A) (a_usp A + -320) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    dinv_L8CG L d ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_L8CG F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -320)) (a_gp A) (a_tp A) x5 (Z_to_bv 64 ((a_S A) + 45436 + 1032 * sv_gSel L)) x7 (Z_to_bv 64 ((a_S A) + 64036)) (Z_to_bv 64 (sv_zn L)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sv_groupPos L)) (Z_to_bv 64 (a_S A)) x20 x21 (Z_to_bv 64 ((a_S A) + 2047)) x23 x24 (Z_to_bv 64 (sv_nSelectors L)) x26 x27 (Z_to_bv 64 (sv_nblock L)) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1e4f8) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition S0F_cut_L8CD (A : act14) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x7 x10 x12 x13 x14 x15 x16 x17 x21 x23 x24 x26 x27 x29 x30 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f184 f200 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96
         (Z_to_bv 64 ((a_S A) + 2124)) (Z_to_bv 64 ((a_S A) + 7884)) (Z_to_bv 64 ((a_S A) + 3152)) (Z_to_bv 64 ((a_S A) + 7820))
         (Z_to_bv 64 (sv_gSel L)) (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 (sv_groupNo L))
         (Z_to_bv 64 ((a_S A) + 57820 + 1032 * sv_gSel L)) (Z_to_bv 64 ((a_S A) + 51628 + 1032 * sv_gSel L)) f184 (Z_to_bv 64 (sv_gMinlen L)) f200 pb ->
    stk s0segs m (a_lo A) (a_usp A + -320) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    dinv_L8 5 L d ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_L8 F 5 L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -320)) (a_gp A) (a_tp A) x5 (Z_to_bv 64 ((a_S A) + 45436 + 1032 * sv_gSel L)) x7 (Z_to_bv 64 ((a_S A) + 64036)) (Z_to_bv 64 (sv_zn L)) x10 (Z_to_bv 64 (d_bsLive d)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sv_groupPos L)) (Z_to_bv 64 (a_S A)) (Z_to_bv 64 ((a_S A) + 3152)) x21 (Z_to_bv 64 ((a_S A) + 2047)) x23 x24 (Z_to_bv 64 (sv_nSelectors L)) x26 x27 (Z_to_bv 64 (sv_nblock L)) x29 x30 (Z_to_bv 64 (sv_zvec L)))
          (a_F A) (Z_to_bv 64 0x1e594) (a_fc A) None m (seg_rom s0segs)).

End ACeilS1.
