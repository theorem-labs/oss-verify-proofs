(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzContracts BzContracts0 DecCut DecAux.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecAuxM DecAuxL S0_dec_U13 S0_decCutsM.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAux OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac.DecAuxB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAuxM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAuxL OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_dec_U13 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_decCutsM.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU9 BzDU10. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF S0F_decRet S0F_decCuts S0F_decCutsM.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU10 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCuts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCutsM.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzImg0TacF.
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition LFAcF (A : act14) (F : nat) (L : dsv) (s : dstrm) (J : jk) (mb : Z -> Z) (pp uc mm : Z) : Prop :=
  forall (x1 x5 x6 x7 x8 x9 x21 x23 x24 x25 x27 x28 x29 x30 x31 : word)
         (d : dst) (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f104 f112 f152 f168 f176 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 ((a_S A) + 2047))
         (Z_to_bv 64 (sv_nblockMAX L)) f104 f112 (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 ((a_S A) + 51628 + 1032 * sv_gSel L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (sv_groupPos L)) f152
         (Z_to_bv 64 ((a_S A) + 57820 + 1032 * sv_gSel L)) f168 f176 (Z_to_bv 64 ((a_S A) + 45436 + 1032 * sv_gSel L)) f192 (Z_to_bv 64 ((a_S A) + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (a_usp A + -336) ->
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
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 (Z_to_bv 64 (-4)) (Z_to_bv 64 uc) (Z_to_bv 64 pp) (Z_to_bv 64 (a_S A + 3724)) (Z_to_bv 64 (18446744073709551615 - (a_S A + 3724))) (Z_to_bv 64 (pp - 3)) (Z_to_bv 64 3) (Z_to_bv 64 mm)
               (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 (a_S A + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 (Z_to_bv 64 (sv_nSelectors L)) x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x274c0) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition LFBcF (A : act14) (F : nat) (L : dsv) (s : dstrm) (J : jk) (mb : Z -> Z) (pp uc k : Z) : Prop :=
  forall (x1 x5 x6 x7 x8 x9 x17 x21 x23 x24 x25 x27 x28 x29 x30 x31 : word)
         (d : dst) (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f104 f112 f152 f168 f176 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 ((a_S A) + 2047))
         (Z_to_bv 64 (sv_nblockMAX L)) f104 f112 (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 ((a_S A) + 51628 + 1032 * sv_gSel L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (sv_groupPos L)) f152
         (Z_to_bv 64 ((a_S A) + 57820 + 1032 * sv_gSel L)) f168 f176 (Z_to_bv 64 ((a_S A) + 45436 + 1032 * sv_gSel L)) f192 (Z_to_bv 64 ((a_S A) + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (a_usp A + -336) ->
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
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 (Z_to_bv 64 (-4)) (Z_to_bv 64 uc) (Z_to_bv 64 pp) (Z_to_bv 64 (a_S A + 3724)) (Z_to_bv 64 (18446744073709551615 - (a_S A + 3724))) (Z_to_bv 64 (pp + k)) (Z_to_bv 64 k) x17
               (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 (a_S A + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 (Z_to_bv 64 (sv_nSelectors L)) x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x2757c) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition LFZcF (A : act14) (F : nat) (L : dsv) (s : dstrm) (J : jk) (mb : Z -> Z) (pp uc : Z) : Prop :=
  forall (x1 x5 x6 x7 x8 x9 x15 x16 x17 x21 x23 x24 x25 x27 x28 x29 x30 x31 : word)
         (d : dst) (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f104 f112 f152 f168 f176 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 ((a_S A) + 2047))
         (Z_to_bv 64 (sv_nblockMAX L)) f104 f112 (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 ((a_S A) + 51628 + 1032 * sv_gSel L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (sv_groupPos L)) f152
         (Z_to_bv 64 ((a_S A) + 57820 + 1032 * sv_gSel L)) f168 f176 (Z_to_bv 64 ((a_S A) + 45436 + 1032 * sv_gSel L)) f192 (Z_to_bv 64 ((a_S A) + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (a_usp A + -336) ->
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
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 (Z_to_bv 64 (-4)) (Z_to_bv 64 uc) (Z_to_bv 64 pp) (Z_to_bv 64 (a_S A + 3724)) (Z_to_bv 64 (18446744073709551615 - (a_S A + 3724))) x15 x16 x17
               (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 (a_S A + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 (Z_to_bv 64 (sv_nSelectors L)) x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x275c4) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition LGHcF (A : act14) (F : nat) (L : dsv) (s : dstrm) (J : jk) (mb : Z -> Z) : Prop :=
  forall (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x17 x21 x23 x24 x25 x27 x28 x29 x30 x31 : word)
         (d : dst) (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f104 f112 f152 f168 f176 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 ((a_S A) + 2047))
         (Z_to_bv 64 (sv_nblockMAX L)) f104 f112 (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 ((a_S A) + 51628 + 1032 * sv_gSel L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (sv_groupPos L)) f152
         (Z_to_bv 64 ((a_S A) + 57820 + 1032 * sv_gSel L)) f168 f176 (Z_to_bv 64 ((a_S A) + 45436 + 1032 * sv_gSel L)) f192 (Z_to_bv 64 ((a_S A) + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (a_usp A + -336) ->
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
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 (Z_to_bv 64 (-4)) x11 x12 x13 x14 (Z_to_bv 64 ((sv_nextSym L - 1) / 16)) (Z_to_bv 64 (sv_nextSym L - 1)) x17
               (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 (a_S A + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 (Z_to_bv 64 (sv_nSelectors L)) x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x2721c) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition LGCcF (A : act14) (F : nat) (L : dsv) (s : dstrm) (J : jk) (mb : Z -> Z) (lno uc k : Z) : Prop :=
  forall (x1 x5 x6 x7 x8 x9 x17 x21 x23 x24 x25 x27 x28 x29 x30 x31 : word)
         (d : dst) (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f104 f112 f152 f168 f176 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 ((a_S A) + 2047))
         (Z_to_bv 64 (sv_nblockMAX L)) f104 f112 (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 ((a_S A) + 51628 + 1032 * sv_gSel L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (sv_groupPos L)) f152
         (Z_to_bv 64 ((a_S A) + 57820 + 1032 * sv_gSel L)) f168 f176 (Z_to_bv 64 ((a_S A) + 45436 + 1032 * sv_gSel L)) f192 (Z_to_bv 64 ((a_S A) + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (a_usp A + -336) ->
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
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 (Z_to_bv 64 (-4)) (Z_to_bv 64 uc) (Z_to_bv 64 (a_S A + 3724)) (Z_to_bv 64 (18446744073709551615 - (a_S A + 3724))) (Z_to_bv 64 (a_S A + 7820 + 4 * lno)) (Z_to_bv 64 lno) (Z_to_bv 64 k) x17
               (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 (a_S A + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 (Z_to_bv 64 (sv_nSelectors L)) x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x27290) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition LGEcF (A : act14) (F : nat) (L : dsv) (s : dstrm) (J : jk) (mb : Z -> Z) (lno uc : Z) : Prop :=
  forall (x1 x6 x7 x8 x9 x16 x17 x21 x23 x24 x25 x27 x28 x29 x30 x31 : word)
         (d : dst) (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f104 f112 f152 f168 f176 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 ((a_S A) + 2047))
         (Z_to_bv 64 (sv_nblockMAX L)) f104 f112 (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 ((a_S A) + 51628 + 1032 * sv_gSel L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (sv_groupPos L)) f152
         (Z_to_bv 64 ((a_S A) + 57820 + 1032 * sv_gSel L)) f168 f176 (Z_to_bv 64 ((a_S A) + 45436 + 1032 * sv_gSel L)) f192 (Z_to_bv 64 ((a_S A) + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (a_usp A + -336) ->
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
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -336)) (a_gp A) (a_tp A) (Z_to_bv 64 (mb lno)) x6 x7 x8 x9 (Z_to_bv 64 (-4)) (Z_to_bv 64 uc) (Z_to_bv 64 (a_S A + 3724)) (Z_to_bv 64 (18446744073709551615 - (a_S A + 3724))) (Z_to_bv 64 (a_S A + 7820 + 4 * lno)) (Z_to_bv 64 lno) x16 x17
               (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 (a_S A + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 (Z_to_bv 64 (sv_nSelectors L)) x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x272d0) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition LGDcF (A : act14) (F : nat) (L : dsv) (s : dstrm) (J : jk) (mb : Z -> Z) (lno uc l : Z) : Prop :=
  forall (x1 x6 x7 x8 x9 x21 x23 x24 x25 x27 x28 x29 x30 x31 : word)
         (d : dst) (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f104 f112 f152 f168 f176 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 ((a_S A) + 2047))
         (Z_to_bv 64 (sv_nblockMAX L)) f104 f112 (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 ((a_S A) + 51628 + 1032 * sv_gSel L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (sv_groupPos L)) f152
         (Z_to_bv 64 ((a_S A) + 57820 + 1032 * sv_gSel L)) f168 f176 (Z_to_bv 64 ((a_S A) + 45436 + 1032 * sv_gSel L)) f192 (Z_to_bv 64 ((a_S A) + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (a_usp A + -336) ->
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
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -336)) (a_gp A) (a_tp A) (Z_to_bv 64 1) x6 x7 x8 x9 (Z_to_bv 64 (-4)) (Z_to_bv 64 uc) (Z_to_bv 64 (a_S A + 3724)) (Z_to_bv 64 (18446744073709551615 - (a_S A + 3724))) (Z_to_bv 64 (18446744073709551615 - (a_S A + 7820))) (Z_to_bv 64 (l - 1)) (Z_to_bv 64 16) (Z_to_bv 64 15)
               (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 (a_S A + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 (Z_to_bv 64 (sv_nSelectors L)) x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x272f8) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition LROcF (A : act14) (F : nat) (L : dsv) (s : dstrm) (J : jk) (mb : Z -> Z) (lno uc ii : Z) : Prop :=
  forall (x1 x5 x6 x7 x8 x9 x16 x21 x23 x24 x25 x27 x28 x29 x30 x31 : word)
         (d : dst) (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f104 f112 f152 f168 f176 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 ((a_S A) + 2047))
         (Z_to_bv 64 (sv_nblockMAX L)) f104 f112 (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 ((a_S A) + 51628 + 1032 * sv_gSel L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (sv_groupPos L)) f152
         (Z_to_bv 64 ((a_S A) + 57820 + 1032 * sv_gSel L)) f168 f176 (Z_to_bv 64 ((a_S A) + 45436 + 1032 * sv_gSel L)) f192 (Z_to_bv 64 ((a_S A) + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (a_usp A + -336) ->
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
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 (Z_to_bv 64 (-4)) (Z_to_bv 64 uc) (Z_to_bv 64 (a_S A + 3724)) (Z_to_bv 64 (18446744073709551615 - (a_S A + 3724))) (Z_to_bv 64 (18446744073709551615 - (a_S A + 7820))) (Z_to_bv 64 (3855 + 16 * ii)) x16 (Z_to_bv 64 ii)
               (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 (a_S A + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 (Z_to_bv 64 (sv_nSelectors L)) x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x273ec) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition LRIcF (A : act14) (F : nat) (L : dsv) (s : dstrm) (J : jk) (mb : Z -> Z) (lno uc ii j : Z) : Prop :=
  forall (x1 x6 x7 x8 x9 x21 x23 x24 x25 x27 x28 x29 x30 x31 : word)
         (d : dst) (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f104 f112 f152 f168 f176 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 ((a_S A) + 2047))
         (Z_to_bv 64 (sv_nblockMAX L)) f104 f112 (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 ((a_S A) + 51628 + 1032 * sv_gSel L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (sv_groupPos L)) f152
         (Z_to_bv 64 ((a_S A) + 57820 + 1032 * sv_gSel L)) f168 f176 (Z_to_bv 64 ((a_S A) + 45436 + 1032 * sv_gSel L)) f192 (Z_to_bv 64 ((a_S A) + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (a_usp A + -336) ->
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
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -336)) (a_gp A) (a_tp A) (Z_to_bv 64 (16 - j)) x6 x7 x8 x9 (Z_to_bv 64 (-4)) (Z_to_bv 64 uc) (Z_to_bv 64 (a_S A + 3724)) (Z_to_bv 64 (18446744073709551615 - (a_S A + 3724))) (Z_to_bv 64 (18446744073709551615 - (a_S A + 7820))) (Z_to_bv 64 (3855 + 16 * ii - j)) (Z_to_bv 64 ii) (Z_to_bv 64 (a_S A + 7820 + 4 * ii))
               (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 (a_S A + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 (Z_to_bv 64 (sv_nSelectors L)) x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x27408) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition LJcF (A : act14) (F : nat) (L : dsv) (s : dstrm) (J : jk) (uc : Z) (mb2 : Z -> Z) : Prop :=
  forall (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x21 x23 x24 x25 x27 x28 x29 x30 x31 : word)
         (d : dst) (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f104 f112 f152 f168 f176 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 ((a_S A) + 2047))
         (Z_to_bv 64 (sv_nblockMAX L)) f104 f112 (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 ((a_S A) + 51628 + 1032 * sv_gSel L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (sv_groupPos L)) f152
         (Z_to_bv 64 ((a_S A) + 57820 + 1032 * sv_gSel L)) f168 f176 (Z_to_bv 64 ((a_S A) + 45436 + 1032 * sv_gSel L)) f192 (Z_to_bv 64 ((a_S A) + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (a_usp A + -336) ->
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
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 (Z_to_bv 64 (-4)) (Z_to_bv 64 uc) x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 (a_S A + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 (Z_to_bv 64 (sv_nSelectors L)) x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x275e0) (a_fc A) None m (seg_rom s0segs)).

End ACeilS1.
