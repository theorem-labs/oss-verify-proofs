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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDU6 BzDUM BzDU7. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU6 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU7 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Export S0F_decRet.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzImg0TacF.
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition S0F_cut_L7T (A : act14) (F : nat) (t : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x26 x28 x29 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f80 f96 f104 f112 f120 f128 f160 f168 f176 f184 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 (Z_to_bv 64 (sv_nSelectors L)) (Z_to_bv 64 ((a_S A) + 64012)) (Z_to_bv 64 ((a_S A) + 57820)) (Z_to_bv 64 ((a_S A) + 45436)) (Z_to_bv 64 ((a_S A) + 51628)) (Z_to_bv 64 (18446744073709551615 - ((a_S A) + 64012))) (Z_to_bv 64 (18446744073709551615 - ((a_S A) + 57820))) (Z_to_bv 64 (18446744073709551615 - ((a_S A) + 51628))) (Z_to_bv 64 (18446744073709551615 - ((a_S A) + 45436))) f80 (Z_to_bv 64 ((a_S A) + 2047)) f96 f104 f112 f120 f128 (Z_to_bv 64 ((a_S A) + 43888)) (Z_to_bv 64 (18446744073709551615 - ((a_S A) + 43888))) (Z_to_bv 64 (sv_nGroups L)) f160 f168 f176 f184 f192 (Z_to_bv 64 ((a_S A) + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (a_usp A + -336) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    (dinv_L7T L d t /\ (t < sv_nGroups L)%Z) ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_L7T F L d s t))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ((a_S A))) x19 (Z_to_bv 64 ((a_S A) + 64036)) (Z_to_bv 64 (sv_alphaSize L)) (Z_to_bv 64 (t)) (Z_to_bv 64 (sv_alphaSize L)) x24 (Z_to_bv 64 ((a_S A) + 43888 + 258 * t)) x26 (Z_to_bv 64 (258)) x28 x29 (Z_to_bv 64 ((a_S A) + 7884)) x31)
          (a_F A) (Z_to_bv 64 0x26984) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition S0F_cut_L7C (A : act14) (F : nat) (t mn mx : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x8 x10 x11 x12 x14 x16 x17 x19 x24 x26 x28 x29 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f80 f96 f104 f112 f120 f128 f160 f168 f176 f184 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 (Z_to_bv 64 (sv_nSelectors L)) (Z_to_bv 64 ((a_S A) + 64012)) (Z_to_bv 64 ((a_S A) + 57820)) (Z_to_bv 64 ((a_S A) + 45436)) (Z_to_bv 64 ((a_S A) + 51628)) (Z_to_bv 64 (18446744073709551615 - ((a_S A) + 64012))) (Z_to_bv 64 (18446744073709551615 - ((a_S A) + 57820))) (Z_to_bv 64 (18446744073709551615 - ((a_S A) + 51628))) (Z_to_bv 64 (18446744073709551615 - ((a_S A) + 45436))) f80 (Z_to_bv 64 ((a_S A) + 2047)) f96 f104 f112 f120 f128 (Z_to_bv 64 ((a_S A) + 43888)) (Z_to_bv 64 (18446744073709551615 - ((a_S A) + 43888))) (Z_to_bv 64 (sv_nGroups L)) f160 f168 f176 f184 f192 (Z_to_bv 64 ((a_S A) + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (a_usp A + -336) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    dinv_L7C L d t mn mx ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_L7C F L d s t mn mx))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 (Z_to_bv 64 (mn)) x10 x11 x12 (Z_to_bv 64 (258 * t)) x14 (Z_to_bv 64 (mx)) x16 x17 (Z_to_bv 64 ((a_S A))) x19 (Z_to_bv 64 ((a_S A) + 64036)) (Z_to_bv 64 (sv_alphaSize L)) (Z_to_bv 64 (t)) (Z_to_bv 64 (sv_alphaSize L)) x24 (Z_to_bv 64 ((a_S A) + 43888 + 258 * t)) x26 (Z_to_bv 64 (258)) x28 x29 (Z_to_bv 64 ((a_S A) + 7884)) x31)
          (a_F A) (Z_to_bv 64 0x269f8) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition S0F_cut_L7D (A : act14) (F : nat) (t : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x28 x29 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f80 f96 f104 f112 f120 f128 f160 f168 f176 f184 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 (Z_to_bv 64 (sv_nSelectors L)) (Z_to_bv 64 ((a_S A) + 64012)) (Z_to_bv 64 ((a_S A) + 57820)) (Z_to_bv 64 ((a_S A) + 45436)) (Z_to_bv 64 ((a_S A) + 51628)) (Z_to_bv 64 (18446744073709551615 - ((a_S A) + 64012))) (Z_to_bv 64 (18446744073709551615 - ((a_S A) + 57820))) (Z_to_bv 64 (18446744073709551615 - ((a_S A) + 51628))) (Z_to_bv 64 (18446744073709551615 - ((a_S A) + 45436))) f80 (Z_to_bv 64 ((a_S A) + 2047)) f96 f104 f112 f120 f128 (Z_to_bv 64 ((a_S A) + 43888)) (Z_to_bv 64 (18446744073709551615 - ((a_S A) + 43888))) (Z_to_bv 64 (sv_nGroups L)) f160 f168 f176 f184 f192 (Z_to_bv 64 ((a_S A) + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (a_usp A + -336) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    dinv_L7T L d (t + 1) /\ (0 <= t < sv_nGroups L)%Z ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_L7T F L d s (t + 1)))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ((a_S A))) x19 (Z_to_bv 64 ((a_S A) + 64036)) (Z_to_bv 64 (sv_alphaSize L)) (Z_to_bv 64 (t + 1)) (Z_to_bv 64 (sv_alphaSize L)) x24 (Z_to_bv 64 ((a_S A) + 43888 + 258 * t)) (Z_to_bv 64 (sv_nSelectors L)) (Z_to_bv 64 (258)) x28 x29 (Z_to_bv 64 ((a_S A) + 7884)) x31)
          (a_F A) (Z_to_bv 64 0x26ab8) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition S0F_cut_H7M (A : act14) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x27 x28 x29 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f80 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 (Z_to_bv 64 ((a_S A) + 64012)) (Z_to_bv 64 ((a_S A) + 57820)) (Z_to_bv 64 ((a_S A) + 45436)) (Z_to_bv 64 ((a_S A) + 51628)) (Z_to_bv 64 (18446744073709551615 - ((a_S A) + 64012))) (Z_to_bv 64 (18446744073709551615 - ((a_S A) + 57820))) (Z_to_bv 64 (18446744073709551615 - ((a_S A) + 51628))) (Z_to_bv 64 (18446744073709551615 - ((a_S A) + 45436))) f80 (Z_to_bv 64 ((a_S A) + 2047)) f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 (Z_to_bv 64 ((a_S A) + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (a_usp A + -336) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    dinv_H7M L d ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_H7M F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ((a_S A))) x19 (Z_to_bv 64 ((a_S A) + 64036)) x21 x22 x23 x24 x25 (Z_to_bv 64 (sv_nSelectors L)) x27 x28 x29 (Z_to_bv 64 ((a_S A) + 7884)) x31)
          (a_F A) (Z_to_bv 64 0x26ac4) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition S0F_cut_L7G (A : act14) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x27 x28 x29 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f80 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 (Z_to_bv 64 ((a_S A) + 64012)) (Z_to_bv 64 ((a_S A) + 57820)) (Z_to_bv 64 ((a_S A) + 45436)) (Z_to_bv 64 ((a_S A) + 51628)) (Z_to_bv 64 (18446744073709551615 - ((a_S A) + 64012))) (Z_to_bv 64 (18446744073709551615 - ((a_S A) + 57820))) (Z_to_bv 64 (18446744073709551615 - ((a_S A) + 51628))) (Z_to_bv 64 (18446744073709551615 - ((a_S A) + 45436))) f80 (Z_to_bv 64 ((a_S A) + 2047)) (Z_to_bv 64 (100000 * d_bs100k d)) f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 (Z_to_bv 64 ((a_S A) + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (a_usp A + -336) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    dinv_L7G L d ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_L7G F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ((a_S A))) (Z_to_bv 64 (sv_alphaSize L - 1)) (Z_to_bv 64 ((a_S A) + 64036)) x21 x22 x23 x24 x25 (Z_to_bv 64 (sv_nSelectors L)) x27 x28 x29 (Z_to_bv 64 ((a_S A) + 7884)) x31)
          (a_F A) (Z_to_bv 64 0x26ba8) (a_fc A) None m (seg_rom s0segs)).

End ACeilS1.
