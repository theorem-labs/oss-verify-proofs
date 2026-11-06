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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts BzContracts0 DecCut DecAux.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecAuxM DecAuxL S0_dec_U13 S0_decCutsM.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDefs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzInv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzContracts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzContracts0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac.DecAuxB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAuxM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAuxL OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_dec_U13 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_decCutsM.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU9 BzDU10 DecCutF S0F_decRet S0F_decCuts S0F_decCutsM.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU10 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decCuts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decCutsM.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzImg0TacF.
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition LFAcF (A : act14) (F : nat) (L : dsv) (s : dstrm) (J : jk) (mb : Z -> Z) (pp uc mm : Z) : Prop :=
  forall (x1 x5 x6 x7 x9 x10 x17 x18 x23 x24 x27 x28 x29 x30 x31 : word)
         (d : dst) (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f72 f80 f88 f96 f184 f200 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 (Z_to_bv 64 (a_S A + 45436 + 1032 * (sv_gSel L))) f72 f80 f88 f96 (Z_to_bv 64 (a_S A + 2124)) (Z_to_bv 64 (a_S A + 7884)) (Z_to_bv 64 (a_S A + 3152)) (Z_to_bv 64 (a_S A + 7820)) (Z_to_bv 64 (sv_gSel L)) (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (a_S A + 57820 + 1032 * (sv_gSel L))) (Z_to_bv 64 (a_S A + 51628 + 1032 * (sv_gSel L))) f184 (Z_to_bv 64 (sv_gMinlen L)) f200 pb ->
    stk s0segs m (a_lo A) (a_usp A + -320) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    fuel_ok F d s ->
    ml_nomtfF L d ->
    mtfa_ok (d_mtfa d) ->
    mtf_inv mb ->
    mbrow d mb ->
    (sv_nblock L < sv_nblockMAX L)%Z ->
    (0 <= uc < 256)%Z ->
    (2 <= sv_nextSym L <= 16)%Z ->
    pp = mb 0%Z ->
    (5 <= mm <= sv_nextSym L)%Z ->
    evt s0segs (QF A (K_LFA F L d s pp (mm - 1) uc))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 (a_S A + 64036)) x9 (Z_to_bv 64 (-4)) (Z_to_bv 64 uc) (Z_to_bv 64 pp) (Z_to_bv 64 (a_S A + 3724)) (Z_to_bv 64 (pp - 1)) (Z_to_bv 64 3) (Z_to_bv 64 mm) x17 x18 (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (sv_nblock L)) (Z_to_bv 64 (sv_nextSym L)) (Z_to_bv 64 (a_S A + 2047)) x23 x24 (Z_to_bv 64 (sv_groupPos L)) (Z_to_bv 64 (sv_nSelectors L)) x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1e20c) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition LFBcF (A : act14) (F : nat) (L : dsv) (s : dstrm) (J : jk) (mb : Z -> Z) (pp uc k : Z) : Prop :=
  forall (x1 x5 x7 x9 x10 x14 x16 x17 x21 x23 x24 x26 x27 x29 x30 x31 : word)
         (d : dst) (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f184 f200 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 (Z_to_bv 64 (a_S A + 2124)) (Z_to_bv 64 (a_S A + 7884)) (Z_to_bv 64 (a_S A + 3152)) (Z_to_bv 64 (a_S A + 7820)) (Z_to_bv 64 (sv_gSel L)) (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (a_S A + 57820 + 1032 * (sv_gSel L))) (Z_to_bv 64 (a_S A + 51628 + 1032 * (sv_gSel L))) f184 (Z_to_bv 64 (sv_gMinlen L)) f200 pb ->
    stk s0segs m (a_lo A) (a_usp A + -320) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    fuel_ok F d s ->
    ml_nomtfF L d ->
    mtfa_ok (d_mtfa d) ->
    mtf_inv mb ->
    mbrow d mb ->
    (sv_nblock L < sv_nblockMAX L)%Z ->
    (0 <= uc < 256)%Z ->
    pp = mb 0%Z ->
    (1 <= k <= 3)%Z ->
    evt s0segs (QF A (K_LFB F L d s pp k uc))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -320)) (a_gp A) (a_tp A) x5 (Z_to_bv 64 (a_S A + 45436 + 1032 * (sv_gSel L))) x7 (Z_to_bv 64 (a_S A + 64036)) x9 (Z_to_bv 64 (-4)) (Z_to_bv 64 uc) (Z_to_bv 64 pp) (Z_to_bv 64 (a_S A + 3724)) x14 (Z_to_bv 64 (pp + k)) x16 x17 (Z_to_bv 64 (sv_groupPos L)) (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (a_S A + 3152)) x21 (Z_to_bv 64 (a_S A + 2047)) x23 x24 (Z_to_bv 64 (sv_nSelectors L)) x26 x27 (Z_to_bv 64 (sv_nblock L)) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1e294) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition LFZcF (A : act14) (F : nat) (L : dsv) (s : dstrm) (J : jk) (mb : Z -> Z) (pp uc : Z) : Prop :=
  forall (x1 x5 x7 x9 x10 x14 x15 x16 x17 x21 x23 x24 x26 x27 x29 x30 x31 : word)
         (d : dst) (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f184 f200 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 (Z_to_bv 64 (a_S A + 2124)) (Z_to_bv 64 (a_S A + 7884)) (Z_to_bv 64 (a_S A + 3152)) (Z_to_bv 64 (a_S A + 7820)) (Z_to_bv 64 (sv_gSel L)) (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (a_S A + 57820 + 1032 * (sv_gSel L))) (Z_to_bv 64 (a_S A + 51628 + 1032 * (sv_gSel L))) f184 (Z_to_bv 64 (sv_gMinlen L)) f200 pb ->
    stk s0segs m (a_lo A) (a_usp A + -320) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    fuel_ok F d s ->
    ml_nomtfF L d ->
    mtfa_ok (d_mtfa d) ->
    mtf_inv mb ->
    mbrow d mb ->
    (sv_nblock L < sv_nblockMAX L)%Z ->
    (0 <= uc < 256)%Z ->
    pp = mb 0%Z ->
    evt s0segs (QF A (K_LFB F L d s pp 0 uc))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -320)) (a_gp A) (a_tp A) x5 (Z_to_bv 64 (a_S A + 45436 + 1032 * (sv_gSel L))) x7 (Z_to_bv 64 (a_S A + 64036)) x9 (Z_to_bv 64 (-4)) (Z_to_bv 64 uc) (Z_to_bv 64 pp) (Z_to_bv 64 (a_S A + 3724)) x14 x15 x16 x17 (Z_to_bv 64 (sv_groupPos L)) (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (a_S A + 3152)) x21 (Z_to_bv 64 (a_S A + 2047)) x23 x24 (Z_to_bv 64 (sv_nSelectors L)) x26 x27 (Z_to_bv 64 (sv_nblock L)) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1e2c0) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition LGHcF (A : act14) (F : nat) (L : dsv) (s : dstrm) (J : jk) (mb : Z -> Z) : Prop :=
  forall (x1 x5 x7 x9 x10 x11 x12 x13 x14 x16 x17 x23 x24 x26 x27 x29 x30 x31 : word)
         (d : dst) (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f184 f200 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 (Z_to_bv 64 (a_S A + 2124)) (Z_to_bv 64 (a_S A + 7884)) (Z_to_bv 64 (a_S A + 3152)) (Z_to_bv 64 (a_S A + 7820)) (Z_to_bv 64 (sv_gSel L)) (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (a_S A + 57820 + 1032 * (sv_gSel L))) (Z_to_bv 64 (a_S A + 51628 + 1032 * (sv_gSel L))) f184 (Z_to_bv 64 (sv_gMinlen L)) f200 pb ->
    stk s0segs m (a_lo A) (a_usp A + -320) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    fuel_ok F d s ->
    ml_nomtfF L d ->
    mtfa_ok (d_mtfa d) ->
    mtf_inv mb ->
    mbrow d mb ->
    (sv_nblock L < sv_nblockMAX L)%Z ->
    (17 <= sv_nextSym L <= 256)%Z ->
    evt s0segs (QF A (K_LGC F L d s ((sv_nextSym L - 1) / 16) (zget (d_mtfbase d) ((sv_nextSym L - 1) / 16) + (sv_nextSym L - 1) mod 16) (zget (d_mtfa d) (zget (d_mtfbase d) ((sv_nextSym L - 1) / 16) + (sv_nextSym L - 1) mod 16))))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -320)) (a_gp A) (a_tp A) x5 (Z_to_bv 64 (a_S A + 45436 + 1032 * (sv_gSel L))) x7 (Z_to_bv 64 (a_S A + 64036)) x9 (Z_to_bv 64 (-4)) x11 x12 x13 x14 (Z_to_bv 64 ((sv_nextSym L) - 1)) x16 x17 (Z_to_bv 64 (sv_groupPos L)) (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (a_S A + 3152)) (Z_to_bv 64 (sv_nextSym L)) (Z_to_bv 64 (a_S A + 2047)) x23 x24 (Z_to_bv 64 (sv_nSelectors L)) x26 x27 (Z_to_bv 64 (sv_nblock L)) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1e2cc) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition LGCcF (A : act14) (F : nat) (L : dsv) (s : dstrm) (J : jk) (mb : Z -> Z) (lno uc k : Z) : Prop :=
  forall (x1 x5 x7 x9 x10 x16 x21 x23 x24 x26 x27 x29 x30 x31 : word)
         (d : dst) (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f184 f200 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 (Z_to_bv 64 (a_S A + 2124)) (Z_to_bv 64 (a_S A + 7884)) (Z_to_bv 64 (a_S A + 3152)) (Z_to_bv 64 (a_S A + 7820)) (Z_to_bv 64 (sv_gSel L)) (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (a_S A + 57820 + 1032 * (sv_gSel L))) (Z_to_bv 64 (a_S A + 51628 + 1032 * (sv_gSel L))) f184 (Z_to_bv 64 (sv_gMinlen L)) f200 pb ->
    stk s0segs m (a_lo A) (a_usp A + -320) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    fuel_ok F d s ->
    ml_nomtfF L d ->
    mtfa_ok (d_mtfa d) ->
    mtf_inv mb ->
    mbrow d mb ->
    (sv_nblock L < sv_nblockMAX L)%Z ->
    (0 <= uc < 256)%Z ->
    (1 <= lno <= 15)%Z ->
    (mb lno < k <= mb lno + 15)%Z ->
    evt s0segs (QF A (K_LGC F L d s lno k uc))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -320)) (a_gp A) (a_tp A) x5 (Z_to_bv 64 (a_S A + 45436 + 1032 * (sv_gSel L))) x7 (Z_to_bv 64 (a_S A + 64036)) x9 (Z_to_bv 64 (-4)) (Z_to_bv 64 uc) (Z_to_bv 64 (a_S A + 3724)) (Z_to_bv 64 (a_S A + 7820 + 4 * lno)) (Z_to_bv 64 lno) (Z_to_bv 64 k) x16 (Z_to_bv 64 (a_S A + 3724 + k)) (Z_to_bv 64 (sv_groupPos L)) (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (a_S A + 3152)) x21 (Z_to_bv 64 (a_S A + 2047)) x23 x24 (Z_to_bv 64 (sv_nSelectors L)) x26 x27 (Z_to_bv 64 (sv_nblock L)) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1e310) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition LGEcF (A : act14) (F : nat) (L : dsv) (s : dstrm) (J : jk) (mb : Z -> Z) (lno uc : Z) : Prop :=
  forall (x1 x5 x7 x9 x10 x15 x17 x21 x23 x24 x26 x27 x29 x30 x31 : word)
         (d : dst) (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f184 f200 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 (Z_to_bv 64 (a_S A + 2124)) (Z_to_bv 64 (a_S A + 7884)) (Z_to_bv 64 (a_S A + 3152)) (Z_to_bv 64 (a_S A + 7820)) (Z_to_bv 64 (sv_gSel L)) (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (a_S A + 57820 + 1032 * (sv_gSel L))) (Z_to_bv 64 (a_S A + 51628 + 1032 * (sv_gSel L))) f184 (Z_to_bv 64 (sv_gMinlen L)) f200 pb ->
    stk s0segs m (a_lo A) (a_usp A + -320) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    fuel_ok F d s ->
    ml_nomtfF L d ->
    mtfa_ok (d_mtfa d) ->
    mtf_inv mb ->
    mbrow d mb ->
    (sv_nblock L < sv_nblockMAX L)%Z ->
    (0 <= uc < 256)%Z ->
    (1 <= lno <= 15)%Z ->
    evt s0segs (QF A (K_LGE F L d s lno uc))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -320)) (a_gp A) (a_tp A) x5 (Z_to_bv 64 (a_S A + 45436 + 1032 * (sv_gSel L))) x7 (Z_to_bv 64 (a_S A + 64036)) x9 (Z_to_bv 64 (-4)) (Z_to_bv 64 uc) (Z_to_bv 64 (a_S A + 3724)) (Z_to_bv 64 (a_S A + 7820 + 4 * lno)) (Z_to_bv 64 lno) x15 (Z_to_bv 64 (mb lno)) x17 (Z_to_bv 64 (sv_groupPos L)) (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (a_S A + 3152)) x21 (Z_to_bv 64 (a_S A + 2047)) x23 x24 (Z_to_bv 64 (sv_nSelectors L)) x26 x27 (Z_to_bv 64 (sv_nblock L)) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1e328) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition LGDcF (A : act14) (F : nat) (L : dsv) (s : dstrm) (J : jk) (mb : Z -> Z) (lno uc l : Z) : Prop :=
  forall (x1 x5 x7 x9 x10 x15 x16 x17 x21 x23 x24 x26 x27 x29 x30 x31 : word)
         (d : dst) (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f184 f200 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 (Z_to_bv 64 (a_S A + 2124)) (Z_to_bv 64 (a_S A + 7884)) (Z_to_bv 64 (a_S A + 3152)) (Z_to_bv 64 (a_S A + 7820)) (Z_to_bv 64 (sv_gSel L)) (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (a_S A + 57820 + 1032 * (sv_gSel L))) (Z_to_bv 64 (a_S A + 51628 + 1032 * (sv_gSel L))) f184 (Z_to_bv 64 (sv_gMinlen L)) f200 pb ->
    stk s0segs m (a_lo A) (a_usp A + -320) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    fuel_ok F d s ->
    ml_nomtfF L d ->
    mtfa_ok (d_mtfa d) ->
    (sv_nblock L < sv_nblockMAX L)%Z ->
    (0 <= uc < 256)%Z ->
    (1 <= lno <= 15)%Z ->
    (1 <= l <= lno)%Z ->
    mtf_inv mb ->
    mbrow d (mb_mid mb lno l) ->
    evt s0segs (QF A (K_LGD F L d s uc l))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -320)) (a_gp A) (a_tp A) x5 (Z_to_bv 64 (a_S A + 45436 + 1032 * (sv_gSel L))) x7 (Z_to_bv 64 (a_S A + 64036)) x9 (Z_to_bv 64 (-4)) (Z_to_bv 64 uc) (Z_to_bv 64 (a_S A + 3724)) (Z_to_bv 64 (a_S A + 7820 + 4 * l)) (Z_to_bv 64 (a_S A + 7820)) x15 x16 x17 (Z_to_bv 64 (sv_groupPos L)) (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (a_S A + 3152)) x21 (Z_to_bv 64 (a_S A + 2047)) x23 x24 (Z_to_bv 64 (sv_nSelectors L)) x26 x27 (Z_to_bv 64 (sv_nblock L)) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1e34c) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition LROcF (A : act14) (F : nat) (L : dsv) (s : dstrm) (J : jk) (mb : Z -> Z) (lno uc ii : Z) : Prop :=
  forall (x1 x6 x7 x9 x10 x16 x17 x21 x23 x24 x26 x27 x28 x29 x30 x31 : word)
         (d : dst) (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f72 f80 f88 f96 f184 f200 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 (Z_to_bv 64 (sv_nblock L)) (Z_to_bv 64 (a_S A + 45436 + 1032 * (sv_gSel L))) f72 f80 f88 f96 (Z_to_bv 64 (a_S A + 2124)) (Z_to_bv 64 (a_S A + 7884)) (Z_to_bv 64 (a_S A + 3152)) (Z_to_bv 64 (a_S A + 7820)) (Z_to_bv 64 (sv_gSel L)) (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (a_S A + 57820 + 1032 * (sv_gSel L))) (Z_to_bv 64 (a_S A + 51628 + 1032 * (sv_gSel L))) f184 (Z_to_bv 64 (sv_gMinlen L)) f200 pb ->
    stk s0segs m (a_lo A) (a_usp A + -320) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    fuel_ok F d s ->
    ml_nomtfF L d ->
    mtfa_ok (d_mtfa d) ->
    (sv_nblock L < sv_nblockMAX L)%Z ->
    (0 <= uc < 256)%Z ->
    (1 <= lno <= 15)%Z ->
    (0 <= ii <= 15)%Z ->
    mtf_inv mb ->
    mb_aft mb lno 0%Z = 0%Z ->
    mbrow d (mb_reb mb lno ii) ->
    evt s0segs (QF A (K_LRO F L d s uc ii))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -320)) (a_gp A) (a_tp A) (Z_to_bv 64 ii) x6 x7 (Z_to_bv 64 (a_S A + 64036)) x9 (Z_to_bv 64 (-4)) (Z_to_bv 64 uc) (Z_to_bv 64 (a_S A + 3724)) (Z_to_bv 64 (a_S A + 3739)) (Z_to_bv 64 15) (Z_to_bv 64 (3855 + 16 * ii)) x16 x17 (Z_to_bv 64 (sv_groupPos L)) (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (a_S A + 3152)) x21 (Z_to_bv 64 (a_S A + 2047)) x23 x24 (Z_to_bv 64 (sv_nSelectors L)) x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1e3bc) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition LRIcF (A : act14) (F : nat) (L : dsv) (s : dstrm) (J : jk) (mb : Z -> Z) (lno uc ii j : Z) : Prop :=
  forall (x1 x9 x10 x21 x23 x24 x26 x27 x28 x29 x30 x31 : word)
         (d : dst) (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f72 f80 f88 f96 f184 f200 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 (Z_to_bv 64 (sv_nblock L)) (Z_to_bv 64 (a_S A + 45436 + 1032 * (sv_gSel L))) f72 f80 f88 f96 (Z_to_bv 64 (a_S A + 2124)) (Z_to_bv 64 (a_S A + 7884)) (Z_to_bv 64 (a_S A + 3152)) (Z_to_bv 64 (a_S A + 7820)) (Z_to_bv 64 (sv_gSel L)) (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (a_S A + 57820 + 1032 * (sv_gSel L))) (Z_to_bv 64 (a_S A + 51628 + 1032 * (sv_gSel L))) f184 (Z_to_bv 64 (sv_gMinlen L)) f200 pb ->
    stk s0segs m (a_lo A) (a_usp A + -320) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    fuel_ok F d s ->
    ml_nomtfF L d ->
    mtfa_ok (d_mtfa d) ->
    (sv_nblock L < sv_nblockMAX L)%Z ->
    (0 <= uc < 256)%Z ->
    (1 <= lno <= 15)%Z ->
    (0 <= ii <= 15)%Z ->
    (1 <= j <= 15)%Z ->
    mtf_inv mb ->
    mb_aft mb lno 0%Z = 0%Z ->
    mbrow d (mb_reb mb lno ii) ->
    evt s0segs (QF A (K_LRI F L d s uc ii j))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -320)) (a_gp A) (a_tp A) (Z_to_bv 64 (a_S A + 7820 + 4 * ii)) (Z_to_bv 64 (j - 1)) (Z_to_bv 64 (a_S A + 3739 - j)) (Z_to_bv 64 (a_S A + 64036)) x9 (Z_to_bv 64 (-4)) (Z_to_bv 64 uc) (Z_to_bv 64 (a_S A + 3724)) (Z_to_bv 64 (a_S A + 3739)) (Z_to_bv 64 15) (Z_to_bv 64 (3855 + 16 * ii)) (Z_to_bv 64 ii) (Z_to_bv 64 (3855 + 16 * ii - j)) (Z_to_bv 64 (sv_groupPos L)) (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (a_S A + 3152)) x21 (Z_to_bv 64 (a_S A + 2047)) x23 x24 (Z_to_bv 64 (sv_nSelectors L)) x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1e3d8) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition LJcF (A : act14) (F : nat) (L : dsv) (s : dstrm) (J : jk) (uc : Z) (mb2 : Z -> Z) : Prop :=
  forall (x1 x5 x7 x9 x10 x12 x13 x14 x15 x16 x17 x21 x23 x24 x26 x27 x29 x30 x31 : word)
         (d : dst) (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f184 f200 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 (Z_to_bv 64 (a_S A + 2124)) (Z_to_bv 64 (a_S A + 7884)) (Z_to_bv 64 (a_S A + 3152)) (Z_to_bv 64 (a_S A + 7820)) (Z_to_bv 64 (sv_gSel L)) (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (a_S A + 57820 + 1032 * (sv_gSel L))) (Z_to_bv 64 (a_S A + 51628 + 1032 * (sv_gSel L))) f184 (Z_to_bv 64 (sv_gMinlen L)) f200 pb ->
    stk s0segs m (a_lo A) (a_usp A + -320) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    fuel_ok F d s ->
    ml_nomtfF L d ->
    mtfa_ok (d_mtfa d) ->
    (sv_nblock L < sv_nblockMAX L)%Z ->
    (0 <= uc < 256)%Z ->
    mtf_inv mb2 ->
    mbrow d mb2 ->
    evt s0segs (QF A (K_LJ F L d s uc))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -320)) (a_gp A) (a_tp A) x5 (Z_to_bv 64 (a_S A + 45436 + 1032 * (sv_gSel L))) x7 (Z_to_bv 64 (a_S A + 64036)) x9 (Z_to_bv 64 (-4)) (Z_to_bv 64 uc) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sv_groupPos L)) (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (a_S A + 3152)) x21 (Z_to_bv 64 (a_S A + 2047)) x23 x24 (Z_to_bv 64 (sv_nSelectors L)) x26 x27 (Z_to_bv 64 (sv_nblock L)) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1e420) (a_fc A) None m (seg_rom s0segs)).

End ACeilS1.
