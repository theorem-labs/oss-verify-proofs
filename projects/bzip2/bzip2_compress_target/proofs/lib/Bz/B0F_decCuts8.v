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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU8 DecCutFB B0F_decV.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU8 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Export B0F_decRet.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition B0F_cut_L8A (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w112 : word)
         (w360 w376 w400 w432 w440 w448 w456 w464 w480 w504 w720 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 (Z_to_bv 64 (S + 3160)) w80 w88 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) w112 (Z_to_bv 64 (S + 2047)) ->
    B0FH A m (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_EOB L)) w360 (Z_to_bv 64 (sv_nSelectors L)) w376 (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 (a_shs A)) w400 (Z_to_bv 64 (S + 51628 + 1032 * sv_gSel L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (sv_groupPos L)) w432 w440 w448 w456 w464 (Z_to_bv 64 (S + 57820 + 1032 * sv_gSel L)) w480 (Z_to_bv 64 (sv_nblock L)) (Z_to_bv 64 (S + 45436 + 1032 * sv_gSel L)) w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) (Z_to_bv 64 (sv_zvec L)) (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_L8 1 L d ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_L8 F 1 L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 (Z_to_bv 64 (sv_zn L)) x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb19a4) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_L8G (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w112 : word)
         (w376 w400 w432 w440 w448 w456 w464 w504 w528 w720 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 (Z_to_bv 64 (S + 3160)) w80 w88 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) w112 (Z_to_bv 64 (S + 2047)) ->
    B0FH A m (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 (sv_N L)) (Z_to_bv 64 (sv_nSelectors L)) w376 (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 (a_shs A)) w400 (Z_to_bv 64 (S + 51628 + 1032 * sv_gSel L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (sv_groupPos L)) w432 w440 w448 w456 w464 (Z_to_bv 64 (S + 57820 + 1032 * sv_gSel L)) (Z_to_bv 64 (sv_es L)) (Z_to_bv 64 (sv_nblock L)) (Z_to_bv 64 (S + 45436 + 1032 * sv_gSel L)) w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) w720 (Z_to_bv 64 (sv_zn L)) w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_L8G L d ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_L8G F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb4c68) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_L8D (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w112 : word)
         (w376 w400 w432 w440 w448 w456 w464 w504 w720 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 (Z_to_bv 64 (S + 3160)) w80 w88 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) w112 (Z_to_bv 64 (S + 2047)) ->
    B0FH A m (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 (sv_N L)) (Z_to_bv 64 (sv_nSelectors L)) w376 (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 (a_shs A)) w400 (Z_to_bv 64 (S + 51628 + 1032 * sv_gSel L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (sv_groupPos L)) w432 w440 w448 w456 w464 (Z_to_bv 64 (S + 57820 + 1032 * sv_gSel L)) (Z_to_bv 64 (sv_es L)) (Z_to_bv 64 (sv_nblock L)) (Z_to_bv 64 (S + 45436 + 1032 * sv_gSel L)) w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) (Z_to_bv 64 (sv_zvec L)) (Z_to_bv 64 (a_shs A + 1)) w720 (Z_to_bv 64 (sv_zn L)) w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_L8 3 L d ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_L8 F 3 L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb5408) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_L8CG (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w112 : word)
         (w360 w376 w400 w432 w440 w448 w456 w464 w480 w504 w528 w720 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 (Z_to_bv 64 (S + 3160)) w80 w88 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) w112 (Z_to_bv 64 (S + 2047)) ->
    B0FH A m (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_EOB L)) w360 (Z_to_bv 64 (sv_nSelectors L)) w376 (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 (a_shs A)) w400 (Z_to_bv 64 (S + 51628 + 1032 * sv_gSel L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (sv_groupPos L)) w432 w440 w448 w456 w464 (Z_to_bv 64 (S + 57820 + 1032 * sv_gSel L)) w480 (Z_to_bv 64 (sv_nblock L)) (Z_to_bv 64 (S + 45436 + 1032 * sv_gSel L)) w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) w720 (Z_to_bv 64 (sv_zn L)) w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_L8CG L d ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_L8CG F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb2d7c) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_L8CD (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w112 : word)
         (w360 w376 w400 w432 w440 w448 w456 w464 w480 w504 w720 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 (Z_to_bv 64 (S + 3160)) w80 w88 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) w112 (Z_to_bv 64 (S + 2047)) ->
    B0FH A m (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_EOB L)) w360 (Z_to_bv 64 (sv_nSelectors L)) w376 (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 (a_shs A)) w400 (Z_to_bv 64 (S + 51628 + 1032 * sv_gSel L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (sv_groupPos L)) w432 w440 w448 w456 w464 (Z_to_bv 64 (S + 57820 + 1032 * sv_gSel L)) w480 (Z_to_bv 64 (sv_nblock L)) (Z_to_bv 64 (S + 45436 + 1032 * sv_gSel L)) w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) (Z_to_bv 64 (sv_zvec L)) (Z_to_bv 64 (a_shs A + 1)) w720 (Z_to_bv 64 (sv_zn L)) w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_L8 5 L d ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_L8 F 5 L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb4f90) (a_fc A) None m (seg_rom b0segs)).

End ACeilS1.
