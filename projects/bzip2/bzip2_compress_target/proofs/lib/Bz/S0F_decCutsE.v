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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU9 BzDU11 DecCutF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU11 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Export S0F_decRet.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzImg0TacF.
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition S0F_cut_HFAST (A : act14) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x24 x25 x26 x27 x29 x30 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96
         (Z_to_bv 64 (a_S A + 2124)) (Z_to_bv 64 (a_S A + 7884)) (Z_to_bv 64 (a_S A + 3152)) (Z_to_bv 64 (a_S A + 7820))
         f136 f144 f152 f160 f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (a_usp A + -320) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    dinv_HFAST L d ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_HFAST F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 (a_S A + 64036)) x9
              x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (a_S A + 3152)) x21
              (Z_to_bv 64 (a_S A + 1096)) x23 x24 x25 x26 x27 (Z_to_bv 64 (sv_nblock L)) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1e920) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition S0F_cut_HSMALL (A : act14) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x24 x25 x26 x27 x29 x30 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96
         (Z_to_bv 64 (a_S A + 2124)) (Z_to_bv 64 (a_S A + 7884)) (Z_to_bv 64 (a_S A + 3152)) (Z_to_bv 64 (a_S A + 7820))
         f136 f144 f152 f160 f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (a_usp A + -320) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    dinv_HSMALL L d ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_HSMALL F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 (a_S A + 64036)) x9
              x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (a_S A + 3152)) x21
              (Z_to_bv 64 (a_S A + 1096)) x23 x24 x25 x26 x27 (Z_to_bv 64 (sv_nblock L)) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1e6cc) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Section U11Cuts.
  Variables (A : act14) (F : nat) (L : dsv) (s : dstrm) (J : jk).
  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).
  Definition L21cF (i : Z) : Prop :=
    forall (x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x21 x23 x24 x25 x26 x27 x29 x30 x31 : word)
           (d : dst) (m : word -> option byte) (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96
         (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 7820))
         f136 f144 f152 f160 f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (usp + -320) ->
    munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    fuel_ok F d s ->
    dinv_L21 L d i ->
    evt s0segs (QF A (K_L21 F L d s i))
      (MS (mkR x1 (Z_to_bv 64 (usp + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 (S + 64036)) x9 (Z_to_bv 64 (-4)) (Z_to_bv 64 (S + 68 + 4 * i)) (Z_to_bv 64 (256 - i)) x13 x14 x15 x16 x17 x18 (Z_to_bv 64 S) (Z_to_bv 64 (S + 3152)) x21 (Z_to_bv 64 (S + 2047)) x23 x24 x25 x26 x27 (Z_to_bv 64 (sv_nblock L)) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1e5d4) (a_fc A) None m (seg_rom s0segs)).
  Definition L22cF (k : Z) : Prop :=
    forall (x1 x5 x6 x7 x9 x13 x14 x16 x17 x18 x21 x23 x24 x25 x26 x27 x29 x30 x31 : word)
           (d : dst) (m : word -> option byte) (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96
         (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 7820))
         f136 f144 f152 f160 f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (usp + -320) ->
    munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    fuel_ok F d s ->
    dinv_L22 L d (k + 1) ->
    evt s0segs (QF A (K_L22 F L d s (k + 1)))
      (MS (mkR x1 (Z_to_bv 64 (usp + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 (S + 64036)) x9 (Z_to_bv 64 (-4)) (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 1100 + 4 * k)) x13 x14 (Z_to_bv 64 (S + 1096)) x16 x17 x18 (Z_to_bv 64 S) (Z_to_bv 64 (S + 3152)) x21 (Z_to_bv 64 (S + 2047)) x23 x24 x25 x26 x27 (Z_to_bv 64 (sv_nblock L)) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1e600) (a_fc A) None m (seg_rom s0segs)).
  Definition L23cF (k : Z) : Prop :=
    forall (x1 x5 x6 x7 x9 x14 x16 x17 x18 x21 x23 x24 x25 x26 x27 x29 x30 x31 : word)
           (d : dst) (m : word -> option byte) (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96
         (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 7820))
         f136 f144 f152 f160 f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (usp + -320) ->
    munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    fuel_ok F d s ->
    dinv_L23 L d (k + 1) ->
    evt s0segs (QF A (K_L23 F L d s (k + 1)))
      (MS (mkR x1 (Z_to_bv 64 (usp + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 (S + 64036)) x9 (Z_to_bv 64 (-4)) (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (psum (zget (d_unzftab d)) k)) (Z_to_bv 64 (S + 1100 + 4 * k)) x14 (Z_to_bv 64 (S + 1096)) x16 x17 x18 (Z_to_bv 64 S) (Z_to_bv 64 (S + 3152)) x21 (Z_to_bv 64 (S + 2047)) x23 x24 x25 x26 x27 (Z_to_bv 64 (sv_nblock L)) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1e618) (a_fc A) None m (seg_rom s0segs)).
  Definition L24cF (i : Z) : Prop :=
    forall (x1 x5 x6 x7 x9 x13 x14 x16 x17 x18 x21 x23 x24 x25 x26 x27 x29 x30 x31 : word)
           (d : dst) (m : word -> option byte) (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96
         (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 7820))
         f136 f144 f152 f160 f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (usp + -320) ->
    munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    fuel_ok F d s ->
    dinv_L24 L d i ->
    evt s0segs (QF A (K_L24 F L d s i))
      (MS (mkR x1 (Z_to_bv 64 (usp + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 (S + 64036)) x9 (Z_to_bv 64 (-4)) (Z_to_bv 64 (257 - i)) (Z_to_bv 64 (S + 1096 + 4 * i)) x13 x14 (Z_to_bv 64 (S + 1096)) x16 x17 x18 (Z_to_bv 64 S) (Z_to_bv 64 (S + 3152)) x21 (Z_to_bv 64 (S + 2047)) x23 x24 x25 x26 x27 (Z_to_bv 64 (sv_nblock L)) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1e638) (a_fc A) None m (seg_rom s0segs)).
  Definition L25cF (i : Z) : Prop :=
    forall (x1 x5 x6 x7 x9 x14 x16 x17 x18 x21 x23 x24 x25 x26 x27 x29 x30 x31 : word)
           (d : dst) (m : word -> option byte) (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96
         (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 7820))
         f136 f144 f152 f160 f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (usp + -320) ->
    munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    fuel_ok F d s ->
    dinv_L25 L d i ->
    evt s0segs (QF A (K_L25 F L d s i))
      (MS (mkR x1 (Z_to_bv 64 (usp + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 (S + 64036)) x9 (Z_to_bv 64 (-4)) (Z_to_bv 64 (S + 1096 + 4 * i)) (Z_to_bv 64 (psum (zget (d_unzftab d)) (i - 1))) (Z_to_bv 64 (257 - i)) x14 (Z_to_bv 64 (S + 1096)) x16 x17 x18 (Z_to_bv 64 S) (Z_to_bv 64 (S + 3152)) x21 (Z_to_bv 64 (S + 2047)) x23 x24 x25 x26 x27 (Z_to_bv 64 (sv_nblock L)) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1e664) (a_fc A) None m (seg_rom s0segs)).
  Definition TcF : Prop :=
    forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x16 x17 x18 x21 x23 x24 x25 x26 x27 x29 x30 x31 : word)
           (d : dst) (m : word -> option byte) (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96
         (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 7820))
         f136 f144 f152 f160 f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (usp + -320) ->
    munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    fuel_ok F d s ->
    dinv_T L d ->
    evt s0segs (QF A (K_T F L d s))
      (MS (mkR x1 (Z_to_bv 64 (usp + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 (S + 64036)) x9 x10 x11 x12 x13 x14 (Z_to_bv 64 (S + 1096)) x16 x17 x18 (Z_to_bv 64 S) (Z_to_bv 64 (S + 3152)) x21 (Z_to_bv 64 (S + 2047)) x23 x24 x25 x26 x27 (Z_to_bv 64 (sv_nblock L)) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1e680) (a_fc A) None m (seg_rom s0segs)).

End U11Cuts.

End ACeilS1.
