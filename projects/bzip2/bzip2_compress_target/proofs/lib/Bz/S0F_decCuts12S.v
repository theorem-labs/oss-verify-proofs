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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts BzContracts0 DecCut DecAux BzLemmasT BzLemmasT2 S0_dec_U13 S0_decCutsM S0_decCutsE.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU9 BzDU11 BzDU12F BzDU12S DecCutF S0F_decRet S0F_decCuts S0F_decCutsM S0F_decCutsE.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU11 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12F OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12S OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decCuts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decCutsM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decCutsE.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzImg0TacF.
Section ACeilS1. Context {ACEIL__ : ACeil}.
Section Sm.
  Variables (A : act14) (F : nat) (L : dsv) (s : dstrm) (J : jk) (sym unz ll16_0 ll4_0 : Z -> Z).
  Notation cx := (a_cx A). Notation S := (b_s (a_cx A)). Notation usp := (bv_unsigned (a_sp A)).

  Definition L26cF (k : Z) : Prop :=
    forall (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x18 x21 x23 x24 x25 x26 x27 x29 x30 x31 : word)
           (d : dst) (m : word -> option byte) (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96
         (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 7820))
         f136 f144 f152 f160 f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (usp + -320) ->
    munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    fuel_ok F d s ->
    smallF L d sym unz ll16_0 ll4_0 ->
    (forall q, zget (d_ll16 d) q = ll16_0 q) ->
    (forall y, zget (d_ll4 d) y = ll4_0 y) ->
    (forall q, 0 <= q < k -> zget (d_cftabCopy d) q = psum unz q)%Z ->
    (0 <= k <= 257)%Z ->
    evt s0segs (QF A (K_L26 F L d s k))
      (MS (mkR x1 (Z_to_bv 64 (usp + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 (S + 64036)) x9 (Z_to_bv 64 (S + 2124 + 4 * k)) x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (S + 2124)) x18 (Z_to_bv 64 S) (Z_to_bv 64 (S + 3152)) x21 (Z_to_bv 64 (S + 1096)) x23 x24 x25 x26 x27 (Z_to_bv 64 (sv_nblock L)) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1e6f0) (a_fc A) None m (seg_rom s0segs)).

  Definition L27cF (i : Z) (fa fb fc : Z -> Z) : Prop :=
    forall (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x18 x21 x23 x24 x25 x26 x27 x29 x30 x31 : word)
           (d : dst) (m : word -> option byte) (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96
         (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 7820))
         f136 f144 f152 f160 f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (usp + -320) ->
    munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    fuel_ok F d s ->
    smallF L d sym unz ll16_0 ll4_0 ->
    tvst unz ll16_0 ll4_0 i = (fa, fb, fc) ->
    (forall q, zget (d_ll16 d) q = fa q) ->
    (forall y, zget (d_ll4 d) y = fb y) ->
    (forall q, 0 <= q < 256 -> zget (d_cftabCopy d) q = fc q)%Z ->
    (0 <= i <= sv_nblock L)%Z ->
    evt s0segs (QF A (K_L27 F L d s i))
      (MS (mkR x1 (Z_to_bv 64 (usp + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 (S + 64036)) x9 (Z_to_bv 64 i) x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (S + 2124)) x18 (Z_to_bv 64 S) (Z_to_bv 64 (S + 3152)) x21 (Z_to_bv 64 (S + 1096)) x23 x24 x25 x26 x27 (Z_to_bv 64 (sv_nblock L)) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1e708) (a_fc A) None m (seg_rom s0segs)).

  Definition PRcF (st : nat) (fa fb : Z -> Z) (i j : Z) : Prop :=
    forall (x1 x5 x6 x7 x9 x11 x12 x13 x14 x16 x18 x21 x23 x24 x25 x26 x27 x29 x30 x31 : word)
           (d : dst) (m : word -> option byte) (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96
         (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 7820))
         f136 f144 f152 f160 f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (usp + -320) ->
    munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    fuel_ok F d s ->
    smallF L d sym unz ll16_0 ll4_0 ->
    prst unz ll16_0 ll4_0 (sv_nblock L) (d_origPtr d) st = (fa, fb, i, j) ->
    (st < ncyc sym unz (sv_nblock L) (d_origPtr d))%nat ->
    (forall q, zget (d_ll16 d) q = fa q) ->
    (forall y, zget (d_ll4 d) y = fb y) ->
    evt s0segs (QF A (K_PR F L d s i j (Datatypes.S (Z.to_nat (sv_nblock L)) - st)%nat))
      (MS (mkR x1 (Z_to_bv 64 (usp + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 (S + 64036)) x9 (Z_to_bv 64 j) x11 x12 x13 x14 (Z_to_bv 64 i) x16 (Z_to_bv 64 (S + 2124)) x18 (Z_to_bv 64 S) (Z_to_bv 64 (sv_nblock L)) x21 (Z_to_bv 64 (S + 1096)) x23 x24 x25 x26 x27 (Z_to_bv 64 (sv_nblock L)) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1e7b4) (a_fc A) None m (seg_rom s0segs)).

  Definition TAILcF (fa fb : Z -> Z) (j5 : Z) : Prop :=
    forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x16 x18 x21 x23 x24 x25 x27 x29 x30 x31 : word)
           (d : dst) (m : word -> option byte) (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96
         (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 7820))
         f136 f144 f152 f160 f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (usp + -320) ->
    munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    fuel_ok F d s ->
    smallF L d sym unz ll16_0 ll4_0 ->
    (forall q, 0 <= fa q < 65536)%Z ->
    (forall y, 0 <= fb y < 256)%Z ->
    (forall q, zget (d_ll16 d) q = fa q) ->
    (forall y, zget (d_ll4 d) y = fb y) ->
    evt s0segs (QF A (K_TAIL F L d s j5))
      (MS (mkR x1 (Z_to_bv 64 (usp + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 (S + 64036)) x9 x10 x11 x12 x13 x14 (Z_to_bv 64 (d_origPtr d)) x16 (Z_to_bv 64 (S + 2124)) x18 (Z_to_bv 64 S) (Z_to_bv 64 (sv_nblock L)) x21 (Z_to_bv 64 (S + 1096)) x23 x24 x25 (Z_to_bv 64 (d_origPtr d)) x27 (Z_to_bv 64 (sv_nblock L)) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1e830) (a_fc A) None m (seg_rom s0segs)).

  Definition GLcF (fa fb fc : Z -> Z) : Prop :=
    forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x18 x21 x23 x24 x25 x26 x27 x29 x30 x31 : word)
           (d : dst) (m : word -> option byte) (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96
         (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 7820))
         f136 f144 f152 f160 f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (usp + -320) ->
    munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    fuel_ok F d s ->
    smallF L d sym unz ll16_0 ll4_0 ->
    tvst unz ll16_0 ll4_0 (sv_nblock L) = (fa, fb, fc) ->
    (forall q, zget (d_ll16 d) q = fa q) ->
    (forall y, zget (d_ll4 d) y = fb y) ->
    (forall q, 0 <= q < 256 -> zget (d_cftabCopy d) q = fc q)%Z ->
    evt s0segs (QF A (K_L27 F L d s (sv_nblock L)))
      (MS (mkR x1 (Z_to_bv 64 (usp + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 (S + 64036)) x9 x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (S + 2124)) x18 (Z_to_bv 64 S) (Z_to_bv 64 (S + 3152)) x21 (Z_to_bv 64 (S + 1096)) x23 x24 x25 x26 x27 (Z_to_bv 64 (sv_nblock L)) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1e774) (a_fc A) None m (seg_rom s0segs)).

  Definition TRcF (fa fb : Z -> Z) (j5 : Z) : Prop :=
    forall (x1 x5 x6 x7 x9 x11 x12 x13 x14 x16 x18 x21 x23 x24 x25 x27 x29 x30 x31 : word)
           (d : dst) (m : word -> option byte) (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d_set_nused (d_set_tPos d (d_origPtr d)) 0) s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96
         (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 7820))
         f136 f144 f152 f160 f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (usp + -320) ->
    munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    fuel_ok F d s ->
    smallF L d sym unz ll16_0 ll4_0 ->
    (forall q, 0 <= fa q < 65536)%Z ->
    (forall y, 0 <= fb y < 256)%Z ->
    (forall q, zget (d_ll16 d) q = fa q) ->
    (forall y, zget (d_ll4 d) y = fb y) ->
    d_rand d = 1%Z ->
    evt s0segs (QF A (DRet BZ_OK (sv_set_j (sv_set_i L (d_origPtr d)) j5) (sft_r d (indexIntoF (d_origPtr d) (d_cftab d)) (get_ll d (d_origPtr d))) s))
      (MS (mkR x1 (Z_to_bv 64 (usp + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 (S + 64036)) x9 (Z_to_bv 64 100000) x11 x12 x13 x14 (Z_to_bv 64 (d_origPtr d)) x16 (Z_to_bv 64 (S + 2124)) x18 (Z_to_bv 64 S) (Z_to_bv 64 (sv_nblock L)) x21 (Z_to_bv 64 (S + 1096)) x23 x24 x25 (Z_to_bv 64 (d_origPtr d)) x27 (Z_to_bv 64 (sv_nblock L)) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1e84c) (a_fc A) None m (seg_rom s0segs)).

  Definition TNcF (fa fb : Z -> Z) (j5 : Z) : Prop :=
    forall (x1 x5 x6 x7 x9 x11 x12 x13 x14 x16 x18 x21 x23 x24 x25 x27 x29 x30 x31 : word)
           (d : dst) (m : word -> option byte) (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d_set_nused (d_set_tPos d (d_origPtr d)) 0) s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96
         (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 7820))
         f136 f144 f152 f160 f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (usp + -320) ->
    munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    fuel_ok F d s ->
    smallF L d sym unz ll16_0 ll4_0 ->
    (forall q, 0 <= fa q < 65536)%Z ->
    (forall y, 0 <= fb y < 256)%Z ->
    (forall q, zget (d_ll16 d) q = fa q) ->
    (forall y, zget (d_ll4 d) y = fb y) ->
    d_rand d = 0%Z ->
    evt s0segs (QF A (DRet BZ_OK (sv_set_j (sv_set_i L (d_origPtr d)) j5) (sft_nr d (indexIntoF (d_origPtr d) (d_cftab d)) (get_ll d (d_origPtr d))) s))
      (MS (mkR x1 (Z_to_bv 64 (usp + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 (S + 64036)) x9 (Z_to_bv 64 100000) x11 x12 x13 x14 (Z_to_bv 64 (d_origPtr d)) x16 (Z_to_bv 64 (S + 2124)) x18 (Z_to_bv 64 S) (Z_to_bv 64 (sv_nblock L)) x21 (Z_to_bv 64 (S + 1096)) x23 x24 x25 (Z_to_bv 64 (d_origPtr d)) x27 (Z_to_bv 64 (sv_nblock L)) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1e994) (a_fc A) None m (seg_rom s0segs)).

End Sm.
End ACeilS1.
