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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 DecCutFB B0F_decV.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Export B0F_decRet.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition B0F_cut_HSEL (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w88 : word)
         (w344 w352 w360 w368 w376 w384 w400 w408 w416 w424 w440 w448 w456 w464 w472 w480 w496 w504 w528 w720 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3160)) (Z_to_bv 64 (S + 3192)) w88 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (a_fb A + 32)) (Z_to_bv 64 (S + 2047)) ->
    B0FH A m w344 w352 w360 w368 w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 w416 w424 (Z_to_bv 64 (sv_alphaSize L)) w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_HSEL L d ->
    fuel_ok F (d) s ->
    evt b0segs (Q (drun F 30 L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb0104) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_L5O (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w88 : word)
         (w344 w352 w360 w368 w376 w384 w400 w408 w416 w424 w440 w448 w456 w472 w480 w496 w504 w528 w720 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3160)) (Z_to_bv 64 (S + 3192)) w88 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (a_fb A + 32)) (Z_to_bv 64 (S + 2047)) ->
    B0FH A m w344 w352 w360 w368 w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 w416 w424 (Z_to_bv 64 (sv_alphaSize L)) w440 w448 w456 (Z_to_bv 64 (sv_nGroups L)) w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_L5O L d ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_L5O F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 (Z_to_bv 64 (sv_nSelectors L)) (Z_to_bv 64 (sv_i L)) x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb0a34) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_L5I (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x7 x12 x13 x14 x15 x16 x19 x21 x23 x24 x25 x29 x30 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w88 : word)
         (w344 w352 w360 w376 w384 w400 w408 w416 w424 w440 w448 w456 w472 w480 w496 w528 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3160)) (Z_to_bv 64 (S + 3192)) w88 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (a_fb A + 32)) (Z_to_bv 64 (S + 2047)) ->
    B0FH A m w344 w352 w360 (Z_to_bv 64 (sv_nSelectors L)) w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 w416 w424 (Z_to_bv 64 (sv_alphaSize L)) w440 w448 w456 (Z_to_bv 64 (sv_nGroups L)) w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 (Z_to_bv 64 (sv_j L)) (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) (Z_to_bv 64 (sv_i L)) w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_L5I L d ->
    fuel_ok F (d) s ->
    evt b0segs (Q (drun F 32 L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) (Z_to_bv 64 (d_bsLive d)) (Z_to_bv 64 32) x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (S + 36)) (Z_to_bv 64 (S + 32)) x12 x13 x14 x15 x16 (Z_to_bv 64 (a_shs A + 4)) (Z_to_bv 64 (-8)) x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) (Z_to_bv 64 (a_shs A + 4)) x29 x30 (Z_to_bv 64 (-1)))
          (a_F A) (Z_to_bv 64 0xb0a9c) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_HUND (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w88 : word)
         (w344 w352 w360 w368 w376 w384 w400 w408 w416 w424 w440 w448 w456 w472 w480 w496 w504 w528 w720 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3160)) (Z_to_bv 64 (S + 3192)) w88 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (a_fb A + 32)) (Z_to_bv 64 (S + 2047)) ->
    B0FH A m w344 w352 w360 w368 w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 w416 w424 (Z_to_bv 64 (sv_alphaSize L)) w440 w448 w456 (Z_to_bv 64 (sv_nGroups L)) w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_HUND L d ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_HUND F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 (Z_to_bv 64 (sv_nSelectors L)) x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb0d2c) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_HCOD (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w88 w112 : word)
         (w344 w352 w360 w376 w384 w400 w408 w416 w424 w440 w448 w456 w472 w480 w496 w504 w528 w720 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3160)) (Z_to_bv 64 (S + 3192)) w88 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) w112 (Z_to_bv 64 (S + 2047)) ->
    B0FH A m w344 w352 w360 (Z_to_bv 64 (sv_nSelectors L)) w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 w416 w424 (Z_to_bv 64 (sv_alphaSize L)) w440 w448 w456 (Z_to_bv 64 (sv_nGroups L)) w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_HCOD L d ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_HCOD F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 (Z_to_bv 64 (sv_t L)) x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb0f3c) (a_fc A) None m (seg_rom b0segs)).

End ACeilS1.
