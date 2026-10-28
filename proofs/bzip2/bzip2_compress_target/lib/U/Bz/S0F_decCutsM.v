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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Export S0F_decRet.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzImg0TacF.
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition S0F_cut_HMTF1 (A : act14) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x25 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f104 f112 f152 f168 f176 f192 f208 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 ((a_S A) + 2047)) (Z_to_bv 64 (sv_nblockMAX L))
         f104 f112 (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 ((a_S A) + 51628 + 1032 * sv_gSel L))
         (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (sv_groupPos L)) f152
         (Z_to_bv 64 ((a_S A) + 57820 + 1032 * sv_gSel L)) f168 f176 (Z_to_bv 64 ((a_S A) + 45436 + 1032 * sv_gSel L))
         f192 (Z_to_bv 64 ((a_S A) + 7820)) f208 (Z_to_bv 64 (sv_zn L)) pb ->
    stk s0segs m (a_lo A) (a_usp A + -336) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    dinv_HMTF1 L d ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_HMTF1 F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16
               x17 (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 ((a_S A) + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 (Z_to_bv 64 (sv_nSelectors L)) x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x26c4c) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition S0F_cut_SYM (A : act14) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f104 f112 f152 f168 f176 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 ((a_S A) + 2047)) (Z_to_bv 64 (sv_nblockMAX L))
         f104 f112 (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 ((a_S A) + 51628 + 1032 * sv_gSel L))
         (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (sv_groupPos L)) f152
         (Z_to_bv 64 ((a_S A) + 57820 + 1032 * sv_gSel L)) f168 f176 (Z_to_bv 64 ((a_S A) + 45436 + 1032 * sv_gSel L))
         f192 (Z_to_bv 64 ((a_S A) + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (a_usp A + -336) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    dinv_SYM L d ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_SYM F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16
               x17 (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 ((a_S A) + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 (Z_to_bv 64 (sv_nSelectors L)) (Z_to_bv 64 (sv_nextSym L)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x271dc) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition S0F_cut_HLIT (A : act14) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f104 f112 f152 f168 f176 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 ((a_S A) + 2047)) (Z_to_bv 64 (sv_nblockMAX L))
         f104 f112 (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 ((a_S A) + 51628 + 1032 * sv_gSel L))
         (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (sv_groupPos L)) f152
         (Z_to_bv 64 ((a_S A) + 57820 + 1032 * sv_gSel L)) f168 f176 (Z_to_bv 64 ((a_S A) + 45436 + 1032 * sv_gSel L))
         f192 (Z_to_bv 64 ((a_S A) + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (a_usp A + -336) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    dinv_HLIT L d ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_HLIT F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16
               x17 (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 ((a_S A) + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 (Z_to_bv 64 (sv_nSelectors L)) (Z_to_bv 64 (sv_nextSym L)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x271f4) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition S0F_cut_HMTFC (A : act14) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f104 f112 f152 f168 f176 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 ((a_S A) + 2047)) (Z_to_bv 64 (sv_nblockMAX L))
         f104 f112 (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 ((a_S A) + 51628 + 1032 * sv_gSel L))
         (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (sv_groupPos L)) f152
         (Z_to_bv 64 ((a_S A) + 57820 + 1032 * sv_gSel L)) f168 f176 (Z_to_bv 64 ((a_S A) + 45436 + 1032 * sv_gSel L))
         f192 (Z_to_bv 64 ((a_S A) + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (a_usp A + -336) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    dinv_HMTFC L d ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_HMTFC F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 (Z_to_bv 64 (-4)) (Z_to_bv 64 (sv_nblock L)) x12 x13 x14 x15 x16
               x17 (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 ((a_S A) + 64036)) x21 x22 x23 x24 x25 (Z_to_bv 64 (sv_nSelectors L)) x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x276ec) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition S0F_cut_HRUN (A : act14) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x21 x23 x24 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f104 f112 f152 f168 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 ((a_S A) + 2047)) (Z_to_bv 64 (sv_nblockMAX L))
         f104 f112 (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 ((a_S A) + 51628 + 1032 * sv_gSel L))
         (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (sv_groupPos L)) f152
         (Z_to_bv 64 ((a_S A) + 57820 + 1032 * sv_gSel L)) f168 (Z_to_bv 64 (sv_es L))
         (Z_to_bv 64 ((a_S A) + 45436 + 1032 * sv_gSel L)) f192 (Z_to_bv 64 ((a_S A) + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (a_usp A + -336) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    dinv_HRUN L d ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_HRUN F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (sv_N L)) x12 x13 x14 x15 x16
               x17 (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 ((a_S A) + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 (Z_to_bv 64 (sv_nSelectors L)) (Z_to_bv 64 (sv_nextSym L)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x28108) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition S0F_cut_HMTFB (A : act14) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x25 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f112 f152 f168 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 ((a_S A) + 2047)) (Z_to_bv 64 (sv_nblockMAX L))
         (Z_to_bv 64 (sv_N L)) f112 (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 ((a_S A) + 51628 + 1032 * sv_gSel L))
         (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (sv_groupPos L)) f152
         (Z_to_bv 64 ((a_S A) + 57820 + 1032 * sv_gSel L)) f168 (Z_to_bv 64 (sv_es L))
         (Z_to_bv 64 ((a_S A) + 45436 + 1032 * sv_gSel L)) f192 (Z_to_bv 64 ((a_S A) + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (a_usp A + -336) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    dinv_HMTFB L d ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_HMTFB F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 (Z_to_bv 64 (-4)) x11 x12 x13 x14 x15 x16
               x17 (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 ((a_S A) + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 (Z_to_bv 64 (sv_nSelectors L)) x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x2816c) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition S0F_cut_HRUNEND (A : act14) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f104 f112 f152 f168 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 ((a_S A) + 2047)) (Z_to_bv 64 (sv_nblockMAX L))
         f104 f112 (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 ((a_S A) + 51628 + 1032 * sv_gSel L))
         (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (sv_groupPos L)) f152
         (Z_to_bv 64 ((a_S A) + 57820 + 1032 * sv_gSel L)) f168 (Z_to_bv 64 (sv_es L))
         (Z_to_bv 64 ((a_S A) + 45436 + 1032 * sv_gSel L)) f192 (Z_to_bv 64 ((a_S A) + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (a_usp A + -336) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    dinv_HRUNEND L d ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_HRUNEND F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 (Z_to_bv 64 (-4)) x11 x12 x13 x14 x15 x16
               x17 (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 ((a_S A) + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 (Z_to_bv 64 (sv_nSelectors L)) (Z_to_bv 64 (sv_nextSym L)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x28718) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition S0F_cut_HEOB (A : act14) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 (a_S A + 2047)) f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192
         (Z_to_bv 64 (a_S A + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (a_usp A + -336) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    dinv_HEOB L d ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_HEOB F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (a_S A)) x19 (Z_to_bv 64 (a_S A + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x27910) (a_fc A) None m (seg_rom s0segs)).

End ACeilS1.
