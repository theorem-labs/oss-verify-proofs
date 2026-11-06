(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzInv BzTables BzContracts.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU10 DecAuxL DecCutFB B0F_decV.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU10 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAuxL OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Export B0F_decRet.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition B0F_cut_LFA (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (mb : Z -> Z) (pp uc mm : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x7 x11 x12 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w112 : word)
         (w360 w376 w400 w432 w440 w448 w456 w464 w480 w504 w528 w720 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 (Z_to_bv 64 (S + 3160)) w80 w88 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) w112 (Z_to_bv 64 (S + 2047)) ->
    B0FH A m (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_EOB L)) w360 (Z_to_bv 64 (sv_nSelectors L)) w376 (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 (a_shs A)) w400 (Z_to_bv 64 (S + 51628 + 1032 * sv_gSel L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (sv_groupPos L)) w432 w440 w448 w456 w464 (Z_to_bv 64 (S + 57820 + 1032 * sv_gSel L)) w480 (Z_to_bv 64 (sv_nblock L)) (Z_to_bv 64 (S + 45436 + 1032 * sv_gSel L)) w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    ml_nomtfF L d ->
    mtfa_ok (d_mtfa d) ->
    mtf_inv mb ->
    mbrow d mb ->
    (sv_nblock L < sv_nblockMAX L)%Z ->
    (0 <= uc < 256)%Z ->
    (2 <= sv_nextSym L <= 16)%Z ->
    pp = mb 0%Z ->
    (5 <= mm <= sv_nextSym L)%Z ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_LFA F L d s pp (mm - 1) uc))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) (Z_to_bv 64 3) (Z_to_bv 64 mm) x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (-4)) x11 x12 (Z_to_bv 64 pp) (Z_to_bv 64 uc) (Z_to_bv 64 (S + 3724)) (Z_to_bv 64 (18446744073709551615 - (S + 3724))) (Z_to_bv 64 (pp - 3)) x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb2894) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_LFB (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (mb : Z -> Z) (pp uc k : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x11 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w112 : word)
         (w360 w376 w400 w432 w440 w448 w456 w464 w480 w504 w528 w720 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 (Z_to_bv 64 (S + 3160)) w80 w88 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) w112 (Z_to_bv 64 (S + 2047)) ->
    B0FH A m (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_EOB L)) w360 (Z_to_bv 64 (sv_nSelectors L)) w376 (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 (a_shs A)) w400 (Z_to_bv 64 (S + 51628 + 1032 * sv_gSel L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (sv_groupPos L)) w432 w440 w448 w456 w464 (Z_to_bv 64 (S + 57820 + 1032 * sv_gSel L)) w480 (Z_to_bv 64 (sv_nblock L)) (Z_to_bv 64 (S + 45436 + 1032 * sv_gSel L)) w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    ml_nomtfF L d ->
    mtfa_ok (d_mtfa d) ->
    mtf_inv mb ->
    mbrow d mb ->
    (sv_nblock L < sv_nblockMAX L)%Z ->
    (0 <= uc < 256)%Z ->
    pp = mb 0%Z ->
    (1 <= k <= 3)%Z ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_LFB F L d s pp k uc))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (-4)) x11 (Z_to_bv 64 (pp + k)) (Z_to_bv 64 pp) (Z_to_bv 64 uc) (Z_to_bv 64 (S + 3724)) (Z_to_bv 64 (18446744073709551615 - (S + 3724))) (Z_to_bv 64 k) x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb2a0c) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_LFZ (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (mb : Z -> Z) (pp uc : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x11 x12 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w112 : word)
         (w360 w376 w400 w432 w440 w448 w456 w464 w480 w504 w528 w720 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 (Z_to_bv 64 (S + 3160)) w80 w88 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) w112 (Z_to_bv 64 (S + 2047)) ->
    B0FH A m (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_EOB L)) w360 (Z_to_bv 64 (sv_nSelectors L)) w376 (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 (a_shs A)) w400 (Z_to_bv 64 (S + 51628 + 1032 * sv_gSel L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (sv_groupPos L)) w432 w440 w448 w456 w464 (Z_to_bv 64 (S + 57820 + 1032 * sv_gSel L)) w480 (Z_to_bv 64 (sv_nblock L)) (Z_to_bv 64 (S + 45436 + 1032 * sv_gSel L)) w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    ml_nomtfF L d ->
    mtfa_ok (d_mtfa d) ->
    mtf_inv mb ->
    mbrow d mb ->
    (sv_nblock L < sv_nblockMAX L)%Z ->
    (0 <= uc < 256)%Z ->
    pp = mb 0%Z ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_LFB F L d s pp 0 uc))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (-4)) x11 x12 (Z_to_bv 64 pp) (Z_to_bv 64 uc) (Z_to_bv 64 (S + 3724)) (Z_to_bv 64 (18446744073709551615 - (S + 3724))) x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb2a8c) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_LGH (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (mb : Z -> Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x6 x7 x11 x12 x13 x14 x15 x16 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w112 : word)
         (w360 w376 w400 w432 w440 w448 w456 w464 w480 w504 w528 w720 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 (Z_to_bv 64 (S + 3160)) w80 w88 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) w112 (Z_to_bv 64 (S + 2047)) ->
    B0FH A m (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_EOB L)) w360 (Z_to_bv 64 (sv_nSelectors L)) w376 (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 (a_shs A)) w400 (Z_to_bv 64 (S + 51628 + 1032 * sv_gSel L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (sv_groupPos L)) w432 w440 w448 w456 w464 (Z_to_bv 64 (S + 57820 + 1032 * sv_gSel L)) w480 (Z_to_bv 64 (sv_nblock L)) (Z_to_bv 64 (S + 45436 + 1032 * sv_gSel L)) w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    ml_nomtfF L d ->
    mtfa_ok (d_mtfa d) ->
    mtf_inv mb ->
    mbrow d mb ->
    (sv_nblock L < sv_nblockMAX L)%Z ->
    (17 <= sv_nextSym L <= 256)%Z ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_LGC F L d s ((sv_nextSym L - 1) / 16) (zget (d_mtfbase d) ((sv_nextSym L - 1) / 16) + (sv_nextSym L - 1) mod 16) (zget (d_mtfa d) (zget (d_mtfbase d) ((sv_nextSym L - 1) / 16) + (sv_nextSym L - 1) mod 16))))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) (Z_to_bv 64 ((sv_nextSym L - 1) / 16)) x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (-4)) x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (sv_nextSym L - 1)) x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb2438) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_LGC (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (mb : Z -> Z) (lno uc k : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x7 x12 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w112 : word)
         (w360 w376 w400 w432 w440 w448 w456 w464 w480 w504 w528 w720 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 (Z_to_bv 64 (S + 3160)) w80 w88 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) w112 (Z_to_bv 64 (S + 2047)) ->
    B0FH A m (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_EOB L)) w360 (Z_to_bv 64 (sv_nSelectors L)) w376 (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 (a_shs A)) w400 (Z_to_bv 64 (S + 51628 + 1032 * sv_gSel L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (sv_groupPos L)) w432 w440 w448 w456 w464 (Z_to_bv 64 (S + 57820 + 1032 * sv_gSel L)) w480 (Z_to_bv 64 (sv_nblock L)) (Z_to_bv 64 (S + 45436 + 1032 * sv_gSel L)) w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    ml_nomtfF L d ->
    mtfa_ok (d_mtfa d) ->
    mtf_inv mb ->
    mbrow d mb ->
    (sv_nblock L < sv_nblockMAX L)%Z ->
    (0 <= uc < 256)%Z ->
    (1 <= lno <= 15)%Z ->
    (mb lno < k <= mb lno + 15)%Z ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_LGC F L d s lno k uc))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) (Z_to_bv 64 lno) (Z_to_bv 64 ((S + 7820 + 4 * lno) / 8 + 2147450880)) x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (-4)) (Z_to_bv 64 (S + 7820 + 4 * lno)) x12 (Z_to_bv 64 k) (Z_to_bv 64 uc) (Z_to_bv 64 (S + 3724)) (Z_to_bv 64 (18446744073709551615 - (S + 3724))) x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb24d8) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_LGE (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (mb : Z -> Z) (lno uc : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x7 x12 x13 x17 x18 x19 x21 x23 x24 x25 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w112 : word)
         (w360 w376 w400 w432 w440 w448 w456 w464 w480 w504 w528 w720 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 (Z_to_bv 64 (S + 3160)) w80 w88 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) w112 (Z_to_bv 64 (S + 2047)) ->
    B0FH A m (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_EOB L)) w360 (Z_to_bv 64 (sv_nSelectors L)) w376 (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 (a_shs A)) w400 (Z_to_bv 64 (S + 51628 + 1032 * sv_gSel L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (sv_groupPos L)) w432 w440 w448 w456 w464 (Z_to_bv 64 (S + 57820 + 1032 * sv_gSel L)) w480 (Z_to_bv 64 (sv_nblock L)) (Z_to_bv 64 (S + 45436 + 1032 * sv_gSel L)) w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    ml_nomtfF L d ->
    mtfa_ok (d_mtfa d) ->
    mtf_inv mb ->
    mbrow d mb ->
    (sv_nblock L < sv_nblockMAX L)%Z ->
    (0 <= uc < 256)%Z ->
    (1 <= lno <= 15)%Z ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_LGE F L d s lno uc))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) (Z_to_bv 64 lno) (Z_to_bv 64 ((S + 7820 + 4 * lno) / 8 + 2147450880)) x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (-4)) (Z_to_bv 64 (S + 7820 + 4 * lno)) x12 x13 (Z_to_bv 64 uc) (Z_to_bv 64 (S + 3724)) (Z_to_bv 64 (18446744073709551615 - (S + 3724))) x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) (Z_to_bv 64 (mb lno)) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb2560) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_LGD (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (mb : Z -> Z) (lno uc l : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x11 x12 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w112 : word)
         (w360 w376 w400 w432 w440 w448 w456 w464 w480 w504 w528 w720 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 (Z_to_bv 64 (S + 3160)) w80 w88 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) w112 (Z_to_bv 64 (S + 2047)) ->
    B0FH A m (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_EOB L)) w360 (Z_to_bv 64 (sv_nSelectors L)) w376 (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 (a_shs A)) w400 (Z_to_bv 64 (S + 51628 + 1032 * sv_gSel L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (sv_groupPos L)) w432 w440 w448 w456 w464 (Z_to_bv 64 (S + 57820 + 1032 * sv_gSel L)) w480 (Z_to_bv 64 (sv_nblock L)) (Z_to_bv 64 (S + 45436 + 1032 * sv_gSel L)) w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    ml_nomtfF L d ->
    mtfa_ok (d_mtfa d) ->
    (sv_nblock L < sv_nblockMAX L)%Z ->
    (0 <= uc < 256)%Z ->
    (1 <= lno <= 15)%Z ->
    (1 <= l <= lno)%Z ->
    mtf_inv mb ->
    mbrow d (mb_mid mb lno l) ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_LGD F L d s uc l))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) (Z_to_bv 64 (l - 1)) (Z_to_bv 64 15) (Z_to_bv 64 1) (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (-4)) x11 x12 (Z_to_bv 64 16) (Z_to_bv 64 uc) (Z_to_bv 64 (S + 3724)) (Z_to_bv 64 (18446744073709551615 - (S + 3724))) (Z_to_bv 64 (18446744073709551615 - (S + 7820))) x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb2590) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_LRO (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (mb : Z -> Z) (lno uc ii : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x6 x7 x12 x13 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w112 : word)
         (w360 w376 w400 w432 w440 w448 w456 w464 w480 w504 w528 w720 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 (Z_to_bv 64 (S + 3160)) w80 w88 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) w112 (Z_to_bv 64 (S + 2047)) ->
    B0FH A m (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_EOB L)) w360 (Z_to_bv 64 (sv_nSelectors L)) w376 (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 (a_shs A)) w400 (Z_to_bv 64 (S + 51628 + 1032 * sv_gSel L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (sv_groupPos L)) w432 w440 w448 w456 w464 (Z_to_bv 64 (S + 57820 + 1032 * sv_gSel L)) w480 (Z_to_bv 64 (sv_nblock L)) (Z_to_bv 64 (S + 45436 + 1032 * sv_gSel L)) w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    ml_nomtfF L d ->
    mtfa_ok (d_mtfa d) ->
    (sv_nblock L < sv_nblockMAX L)%Z ->
    (0 <= uc < 256)%Z ->
    (1 <= lno <= 15)%Z ->
    (0 <= ii <= 15)%Z ->
    mtf_inv mb ->
    mb_aft mb lno 0%Z = 0%Z ->
    mbrow d (mb_reb mb lno ii) ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_LRO F L d s uc ii))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) (Z_to_bv 64 (3855 + 16 * ii)) x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (-4)) (Z_to_bv 64 ii) x12 x13 (Z_to_bv 64 uc) (Z_to_bv 64 (S + 3724)) (Z_to_bv 64 (18446744073709551615 - (S + 3724))) (Z_to_bv 64 (18446744073709551615 - (S + 7820))) x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb273c) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_LRI (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (mb : Z -> Z) (lno uc ii j : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x7 x12 x13 x18 x19 x21 x23 x24 x25 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w112 : word)
         (w360 w376 w400 w432 w440 w448 w456 w464 w480 w504 w528 w720 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 (Z_to_bv 64 (S + 3160)) w80 w88 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) w112 (Z_to_bv 64 (S + 2047)) ->
    B0FH A m (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_EOB L)) w360 (Z_to_bv 64 (sv_nSelectors L)) w376 (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 (a_shs A)) w400 (Z_to_bv 64 (S + 51628 + 1032 * sv_gSel L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (sv_groupPos L)) w432 w440 w448 w456 w464 (Z_to_bv 64 (S + 57820 + 1032 * sv_gSel L)) w480 (Z_to_bv 64 (sv_nblock L)) (Z_to_bv 64 (S + 45436 + 1032 * sv_gSel L)) w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    ml_nomtfF L d ->
    mtfa_ok (d_mtfa d) ->
    (sv_nblock L < sv_nblockMAX L)%Z ->
    (0 <= uc < 256)%Z ->
    (1 <= lno <= 15)%Z ->
    (0 <= ii <= 15)%Z ->
    (0 <= j <= 15)%Z ->
    mtf_inv mb ->
    mb_aft mb lno 0%Z = 0%Z ->
    mbrow d (mb_reb mb lno ii) ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_LRI F L d s uc ii j))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) (Z_to_bv 64 (3855 + 16 * ii - j)) (Z_to_bv 64 ii) x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (-4)) (Z_to_bv 64 (S + 7820 + 4 * ii)) x12 x13 (Z_to_bv 64 uc) (Z_to_bv 64 (S + 3724)) (Z_to_bv 64 (18446744073709551615 - (S + 3724))) (Z_to_bv 64 (18446744073709551615 - (S + 7820))) x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) (Z_to_bv 64 (16 - j)) (Z_to_bv 64 ((S + 7820 + 4 * ii) / 8 + 2147450880)) x30 x31)
          (a_F A) (Z_to_bv 64 0xb2764) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_LJ (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (uc : Z) (mb2 : Z -> Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x11 x12 x13 x15 x16 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w112 : word)
         (w360 w376 w400 w432 w440 w448 w456 w464 w480 w504 w528 w720 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 (Z_to_bv 64 (S + 3160)) w80 w88 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) w112 (Z_to_bv 64 (S + 2047)) ->
    B0FH A m (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_EOB L)) w360 (Z_to_bv 64 (sv_nSelectors L)) w376 (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 (a_shs A)) w400 (Z_to_bv 64 (S + 51628 + 1032 * sv_gSel L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (sv_groupPos L)) w432 w440 w448 w456 w464 (Z_to_bv 64 (S + 57820 + 1032 * sv_gSel L)) w480 (Z_to_bv 64 (sv_nblock L)) (Z_to_bv 64 (S + 45436 + 1032 * sv_gSel L)) w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    ml_nomtfF L d ->
    mtfa_ok (d_mtfa d) ->
    (sv_nblock L < sv_nblockMAX L)%Z ->
    (0 <= uc < 256)%Z ->
    mtf_inv mb2 ->
    mbrow d mb2 ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_LJ F L d s uc))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (-4)) x11 x12 x13 (Z_to_bv 64 uc) x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb2ab8) (a_fc A) None m (seg_rom b0segs)).

End ACeilS1.
