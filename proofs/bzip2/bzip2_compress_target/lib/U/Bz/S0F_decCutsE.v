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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU9 BzDU11. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU11 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Export S0F_decRet.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzImg0TacF.
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition S0F_cut_HFAST (A : act14) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x24 x26 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 (a_S A + 2047)) f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192
         (Z_to_bv 64 (a_S A + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (a_usp A + -336) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    dinv_HFAST L d ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_HFAST F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (a_S A)) x19 (Z_to_bv 64 (a_S A + 64036)) (Z_to_bv 64 (a_S A + 1096)) (Z_to_bv 64 (sv_nblock L)) x23 x24 (Z_to_bv 64 (18446744073709551615 - (a_S A + 1096))) x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x27e28) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition S0F_cut_HSMALL (A : act14) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x24 x26 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 (a_S A + 2047)) f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192
         (Z_to_bv 64 (a_S A + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (a_usp A + -336) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    dinv_HSMALL L d ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_HSMALL F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (a_S A)) x19 (Z_to_bv 64 (a_S A + 64036)) (Z_to_bv 64 (a_S A + 1096)) (Z_to_bv 64 (sv_nblock L)) x23 x24 (Z_to_bv 64 (18446744073709551615 - (a_S A + 1096))) x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x27a64) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Section U11Cuts.
  Variables (A : act14) (F : nat) (L : dsv) (s : dstrm) (J : jk).
  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).
  Definition L21cF (i : Z) : Prop :=
    forall (x1 x5 x6 x7 x8 x15 x16 x17 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (d : dst) (m : word -> option byte) (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 (S + 2047)) f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192
         (Z_to_bv 64 (S + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (usp + -336) ->
    munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    fuel_ok F d s ->
    dinv_L21 L d i ->
    evt s0segs (QF A (K_L21 F L d s i))
      (MS (mkR x1 (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 (Z_to_bv 64 i) (Z_to_bv 64 (-4)) (Z_to_bv 64 (18446744073709551615 - (S + 68))) (Z_to_bv 64 (4 * i)) (Z_to_bv 64 (S + 68)) (Z_to_bv 64 1024) x15 x16 x17 (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x27934) (a_fc A) None m (seg_rom s0segs)).
  Definition L22cF (k : Z) : Prop :=
    forall (x1 x5 x6 x7 x8 x9 x16 x17 x19 x23 x24 x26 x27 x28 x29 x30 x31 : word)
           (d : dst) (m : word -> option byte) (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 (S + 2047)) f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192
         (Z_to_bv 64 (S + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (usp + -336) ->
    munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    fuel_ok F d s ->
    dinv_L22 L d (k + 1) ->
    evt s0segs (QF A (K_L22 F L d s (k + 1)))
      (MS (mkR x1 (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 (Z_to_bv 64 (-4)) (Z_to_bv 64 (18446744073709551615 - (S + 68))) (Z_to_bv 64 (4 * k)) (Z_to_bv 64 (4 * k + 4)) (Z_to_bv 64 1024) (Z_to_bv 64 (S + 4 * k)) x16 x17 (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 (S + 1096)) (Z_to_bv 64 (sv_nblock L)) x23 x24 (Z_to_bv 64 (18446744073709551615 - (S + 1096))) x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x27974) (a_fc A) None m (seg_rom s0segs)).
  Definition L23cF (k : Z) : Prop :=
    forall (x1 x5 x6 x7 x8 x9 x15 x16 x17 x19 x23 x24 x26 x27 x28 x29 x30 x31 : word)
           (d : dst) (m : word -> option byte) (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 (S + 2047)) f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192
         (Z_to_bv 64 (S + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (usp + -336) ->
    munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    fuel_ok F d s ->
    dinv_L23 L d (k + 1) ->
    evt s0segs (QF A (K_L23 F L d s (k + 1)))
      (MS (mkR x1 (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 (Z_to_bv 64 (-4)) (Z_to_bv 64 (S + 1100 + 4 * k)) (Z_to_bv 64 (psum (zget (d_unzftab d)) k)) (Z_to_bv 64 (4 * k + 4)) (Z_to_bv 64 (256 - k)) x15 x16 x17 (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 (S + 1096)) (Z_to_bv 64 (sv_nblock L)) x23 x24 (Z_to_bv 64 (18446744073709551615 - (S + 1096))) x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x279a4) (a_fc A) None m (seg_rom s0segs)).
  Definition L24cF (i : Z) : Prop :=
    forall (x1 x5 x6 x7 x8 x13 x14 x15 x16 x17 x19 x23 x24 x26 x27 x28 x29 x30 x31 : word)
           (d : dst) (m : word -> option byte) (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 (S + 2047)) f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192
         (Z_to_bv 64 (S + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (usp + -336) ->
    munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    fuel_ok F d s ->
    dinv_L24 L d i ->
    evt s0segs (QF A (K_L24 F L d s i))
      (MS (mkR x1 (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 (Z_to_bv 64 i) (Z_to_bv 64 (-4)) (Z_to_bv 64 (4 * i)) (Z_to_bv 64 1028) x13 x14 x15 x16 x17 (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 (S + 1096)) (Z_to_bv 64 (sv_nblock L)) x23 x24 (Z_to_bv 64 (18446744073709551615 - (S + 1096))) x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x279dc) (a_fc A) None m (seg_rom s0segs)).
  Definition L25cF (i : Z) : Prop :=
    forall (x1 x5 x6 x7 x8 x15 x16 x17 x19 x23 x24 x26 x27 x28 x29 x30 x31 : word)
           (d : dst) (m : word -> option byte) (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 (S + 2047)) f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192
         (Z_to_bv 64 (S + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (usp + -336) ->
    munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    fuel_ok F d s ->
    dinv_L25 L d i ->
    evt s0segs (QF A (K_L25 F L d s i))
      (MS (mkR x1 (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 (Z_to_bv 64 i) (Z_to_bv 64 (-4)) (Z_to_bv 64 (S + 1096 + 4 * i)) (Z_to_bv 64 (4 * i)) (Z_to_bv 64 (257 - i)) (Z_to_bv 64 (psum (zget (d_unzftab d)) (i - 1))) x15 x16 x17 (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 (S + 1096)) (Z_to_bv 64 (sv_nblock L)) x23 x24 (Z_to_bv 64 (18446744073709551615 - (S + 1096))) x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x27a10) (a_fc A) None m (seg_rom s0segs)).
  Definition TcF : Prop :=
    forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x24 x26 x27 x28 x29 x30 x31 : word)
           (d : dst) (m : word -> option byte) (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 (S + 2047)) f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192
         (Z_to_bv 64 (S + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (usp + -336) ->
    munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    fuel_ok F d s ->
    dinv_T L d ->
    evt s0segs (QF A (K_T F L d s))
      (MS (mkR x1 (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 (S + 1096)) (Z_to_bv 64 (sv_nblock L)) x23 x24 (Z_to_bv 64 (18446744073709551615 - (S + 1096))) x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x27a34) (a_fc A) None m (seg_rom s0segs)).

End U11Cuts.

End ACeilS1.
