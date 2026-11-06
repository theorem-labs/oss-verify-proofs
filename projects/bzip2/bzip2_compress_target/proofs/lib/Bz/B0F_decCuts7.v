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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDU6 BzDU7 DecCutFB B0F_decV.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU6 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU7 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Export B0F_decRet.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition B0F_cut_L7T (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (t : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 : word)
         (w344 w352 w360 w376 w384 w400 w408 w440 w456 w464 w472 w480 w496 w504 w528 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 64012)) (Z_to_bv 64 (S + 57820)) (Z_to_bv 64 (S + 45436)) (Z_to_bv 64 (S + 51628)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3160)) (Z_to_bv 64 (S + 3192)) (Z_to_bv 64 (18446744073709551615 - (S + 64012))) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (18446744073709551615 - (S + 57820))) (Z_to_bv 64 (S + 2047)) ->
    B0FH A m w344 w352 w360 (Z_to_bv 64 (sv_nSelectors L)) w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 (Z_to_bv 64 (18446744073709551615 - (S + 51628))) (Z_to_bv 64 (18446744073709551615 - (S + 45436))) (Z_to_bv 64 (sv_alphaSize L)) w440 (Z_to_bv 64 (sv_nGroups L)) w456 w464 w472 w480 (Z_to_bv 64 (S + 43888)) w496 w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) (Z_to_bv 64 (18446744073709551615 - (S + 43888))) w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    (dinv_L7T L d t /\ (t < sv_nGroups L)%Z) ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_L7T F L d s t))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (S + 43888 + 258 * t)) (Z_to_bv 64 (S + 43888 + 258 * t)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 258) (Z_to_bv 64 2147450880) x23 (Z_to_bv 64 t) (Z_to_bv 64 (sv_alphaSize L)) (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb1220) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_L7I (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (t i mn mx : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x14 x16 x17 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 : word)
         (w344 w352 w360 w376 w384 w400 w408 w440 w456 w464 w472 w480 w496 w504 w528 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 64012)) (Z_to_bv 64 (S + 57820)) (Z_to_bv 64 (S + 45436)) (Z_to_bv 64 (S + 51628)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3160)) (Z_to_bv 64 (S + 3192)) (Z_to_bv 64 (18446744073709551615 - (S + 64012))) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (18446744073709551615 - (S + 57820))) (Z_to_bv 64 (S + 2047)) ->
    B0FH A m w344 w352 w360 (Z_to_bv 64 (sv_nSelectors L)) w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 (Z_to_bv 64 (18446744073709551615 - (S + 51628))) (Z_to_bv 64 (18446744073709551615 - (S + 45436))) (Z_to_bv 64 (sv_alphaSize L)) w440 (Z_to_bv 64 (sv_nGroups L)) w456 w464 w472 w480 (Z_to_bv 64 (S + 43888)) w496 w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) (Z_to_bv 64 (18446744073709551615 - (S + 43888))) w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    (dinv_L7I L d t i mn mx /\ (i < sv_alphaSize L)%Z) ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_L7I F L d s t i mn mx))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 (Z_to_bv 64 i) (Z_to_bv 64 (18446744073709551615 - (S + 43888 + 258 * t))) (Z_to_bv 64 (258 * t)) x14 (Z_to_bv 64 mx) x16 x17 (Z_to_bv 64 (S + 43888 + 258 * t)) (Z_to_bv 64 (S + 43888 + 258 * t)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 258) (Z_to_bv 64 2147450880) (Z_to_bv 64 mn) (Z_to_bv 64 t) (Z_to_bv 64 (sv_alphaSize L)) (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb1258) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_L7C (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (t mn mx : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x11 x12 x14 x16 x17 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 : word)
         (w344 w352 w360 w376 w384 w400 w408 w440 w456 w464 w472 w480 w496 w504 w528 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 64012)) (Z_to_bv 64 (S + 57820)) (Z_to_bv 64 (S + 45436)) (Z_to_bv 64 (S + 51628)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3160)) (Z_to_bv 64 (S + 3192)) (Z_to_bv 64 (18446744073709551615 - (S + 64012))) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (18446744073709551615 - (S + 57820))) (Z_to_bv 64 (S + 2047)) ->
    B0FH A m w344 w352 w360 (Z_to_bv 64 (sv_nSelectors L)) w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 (Z_to_bv 64 (18446744073709551615 - (S + 51628))) (Z_to_bv 64 (18446744073709551615 - (S + 45436))) (Z_to_bv 64 (sv_alphaSize L)) w440 (Z_to_bv 64 (sv_nGroups L)) w456 w464 w472 w480 (Z_to_bv 64 (S + 43888)) w496 w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) (Z_to_bv 64 (18446744073709551615 - (S + 43888))) w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_L7C L d t mn mx ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_L7C F L d s t mn mx))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 (Z_to_bv 64 (258 * t)) x14 (Z_to_bv 64 mx) x16 x17 (Z_to_bv 64 (S + 43888 + 258 * t)) (Z_to_bv 64 (S + 43888 + 258 * t)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 258) (Z_to_bv 64 2147450880) (Z_to_bv 64 mn) (Z_to_bv 64 t) (Z_to_bv 64 (sv_alphaSize L)) (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb12b0) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_HBCR (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (t mn mx : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 : word)
         (w344 w352 w360 w376 w384 w400 w408 w440 w456 w464 w472 w480 w496 w504 w528 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (mt_rows t (sv_alphaSize L) d mn mx) s) ->
    B0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 64012)) (Z_to_bv 64 (S + 57820)) (Z_to_bv 64 (S + 45436)) (Z_to_bv 64 (S + 51628)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3160)) (Z_to_bv 64 (S + 3192)) (Z_to_bv 64 (18446744073709551615 - (S + 64012))) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (18446744073709551615 - (S + 57820))) (Z_to_bv 64 (S + 2047)) ->
    B0FH A m w344 w352 w360 (Z_to_bv 64 (sv_nSelectors L)) w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 (Z_to_bv 64 (18446744073709551615 - (S + 51628))) (Z_to_bv 64 (18446744073709551615 - (S + 45436))) (Z_to_bv 64 (sv_alphaSize L)) w440 (Z_to_bv 64 (sv_nGroups L)) w456 w464 w472 w480 (Z_to_bv 64 (S + 43888)) w496 w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) (Z_to_bv 64 (18446744073709551615 - (S + 43888))) w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_L7C L d t mn mx ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_L7C F L d s t mn mx))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (S + 43888 + 258 * t)) (Z_to_bv 64 (S + 43888 + 258 * t)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 258) (Z_to_bv 64 2147450880) (Z_to_bv 64 mn) (Z_to_bv 64 t) (Z_to_bv 64 (sv_alphaSize L)) (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb131c) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_L7D (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (t : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 : word)
         (w344 w352 w360 w376 w384 w400 w408 w440 w456 w464 w472 w480 w496 w504 w528 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 64012)) (Z_to_bv 64 (S + 57820)) (Z_to_bv 64 (S + 45436)) (Z_to_bv 64 (S + 51628)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3160)) (Z_to_bv 64 (S + 3192)) (Z_to_bv 64 (18446744073709551615 - (S + 64012))) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (18446744073709551615 - (S + 57820))) (Z_to_bv 64 (S + 2047)) ->
    B0FH A m w344 w352 w360 (Z_to_bv 64 (sv_nSelectors L)) w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 (Z_to_bv 64 (18446744073709551615 - (S + 51628))) (Z_to_bv 64 (18446744073709551615 - (S + 45436))) (Z_to_bv 64 (sv_alphaSize L)) w440 (Z_to_bv 64 (sv_nGroups L)) w456 w464 w472 w480 (Z_to_bv 64 (S + 43888)) w496 w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) (Z_to_bv 64 (18446744073709551615 - (S + 43888))) w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    (dinv_L7T L d (t + 1) /\ (0 <= t < sv_nGroups L)%Z) ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_L7T F L d s (t + 1)))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (S + 43888 + 258 * t)) (Z_to_bv 64 (S + 43888 + 258 * t)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 258) (Z_to_bv 64 2147450880) x23 (Z_to_bv 64 (t + 1)) (Z_to_bv 64 (sv_alphaSize L)) (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb134c) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_H7M (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 : word)
         (w344 w352 w360 w376 w384 w400 w408 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 w528 w720 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 64012)) (Z_to_bv 64 (S + 57820)) (Z_to_bv 64 (S + 45436)) (Z_to_bv 64 (S + 51628)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3160)) (Z_to_bv 64 (S + 3192)) (Z_to_bv 64 (18446744073709551615 - (S + 64012))) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (18446744073709551615 - (S + 57820))) (Z_to_bv 64 (S + 2047)) ->
    B0FH A m w344 w352 w360 (Z_to_bv 64 (sv_nSelectors L)) w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 (Z_to_bv 64 (18446744073709551615 - (S + 51628))) (Z_to_bv 64 (18446744073709551615 - (S + 45436))) w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_H7M L d ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_H7M F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb1370) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_L7K (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (ii : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w80 : word)
         (w360 w376 w384 w400 w408 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 w528 w720 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 64012)) (Z_to_bv 64 (S + 57820)) (Z_to_bv 64 (S + 45436)) (Z_to_bv 64 (S + 51628)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3160)) w80 (Z_to_bv 64 (18446744073709551615 - (S + 64012))) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (18446744073709551615 - (S + 57820))) (Z_to_bv 64 (S + 2047)) ->
    B0FH A m (Z_to_bv 64 (100000 * d_bs100k d)) (Z_to_bv 64 (sv_alphaSize L - 1)) w360 (Z_to_bv 64 (sv_nSelectors L)) w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 (Z_to_bv 64 (18446744073709551615 - (S + 51628))) (Z_to_bv 64 (18446744073709551615 - (S + 45436))) w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    (dinv_L7K L d ii /\ 0 <= ii)%Z ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_L7K F L d s ii))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 ii) (Z_to_bv 64 (S + 3724)) (Z_to_bv 64 (16 * ii + 15)) (Z_to_bv 64 (18446744073709551615 - (S + 3724))) (Z_to_bv 64 (S + 7820)) (Z_to_bv 64 (18446744073709551615 - (S + 7820))) (Z_to_bv 64 (3855 + 16 * ii)) x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb1444) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_L7J (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (ii dd : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x7 x10 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w80 : word)
         (w360 w376 w384 w400 w408 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 w528 w720 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 64012)) (Z_to_bv 64 (S + 57820)) (Z_to_bv 64 (S + 45436)) (Z_to_bv 64 (S + 51628)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3160)) w80 (Z_to_bv 64 (18446744073709551615 - (S + 64012))) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (18446744073709551615 - (S + 57820))) (Z_to_bv 64 (S + 2047)) ->
    B0FH A m (Z_to_bv 64 (100000 * d_bs100k d)) (Z_to_bv 64 (sv_alphaSize L - 1)) w360 (Z_to_bv 64 (sv_nSelectors L)) w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 (Z_to_bv 64 (18446744073709551615 - (S + 51628))) (Z_to_bv 64 (18446744073709551615 - (S + 45436))) w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    (dinv_L7J L d ii dd /\ dd <= 15)%Z ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_L7J F L d s ii dd))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) (Z_to_bv 64 (dd - 16)) (Z_to_bv 64 (16 * ii + 15 - dd)) x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 (Z_to_bv 64 (S + 3724)) (Z_to_bv 64 (16 * ii + 15)) (Z_to_bv 64 (18446744073709551615 - (S + 3724))) (Z_to_bv 64 (S + 7820)) (Z_to_bv 64 (18446744073709551615 - (S + 7820))) (Z_to_bv 64 (3855 + 16 * ii - dd)) (Z_to_bv 64 ii) x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb1450) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_L7G (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w80 : word)
         (w360 w376 w384 w400 w408 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 w528 w720 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 64012)) (Z_to_bv 64 (S + 57820)) (Z_to_bv 64 (S + 45436)) (Z_to_bv 64 (S + 51628)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3160)) w80 (Z_to_bv 64 (18446744073709551615 - (S + 64012))) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (18446744073709551615 - (S + 57820))) (Z_to_bv 64 (S + 2047)) ->
    B0FH A m (Z_to_bv 64 (100000 * d_bs100k d)) (Z_to_bv 64 (sv_alphaSize L - 1)) w360 (Z_to_bv 64 (sv_nSelectors L)) w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 (Z_to_bv 64 (18446744073709551615 - (S + 51628))) (Z_to_bv 64 (18446744073709551615 - (S + 45436))) w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_L7G L d ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_L7G F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb14e0) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_call_HBC (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (t mn mx : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x5 x6 x7 x17 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 : word)
         (w344 w352 w360 w376 w384 w400 w408 w440 w456 w464 w472 w480 w496 w504 w528 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 64012)) (Z_to_bv 64 (S + 57820)) (Z_to_bv 64 (S + 45436)) (Z_to_bv 64 (S + 51628)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3160)) (Z_to_bv 64 (S + 3192)) (Z_to_bv 64 (18446744073709551615 - (S + 64012))) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (18446744073709551615 - (S + 57820))) (Z_to_bv 64 (S + 2047)) ->
    B0FH A m w344 w352 w360 (Z_to_bv 64 (sv_nSelectors L)) w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 (Z_to_bv 64 (18446744073709551615 - (S + 51628))) (Z_to_bv 64 (18446744073709551615 - (S + 45436))) (Z_to_bv 64 (sv_alphaSize L)) w440 (Z_to_bv 64 (sv_nGroups L)) w456 w464 w472 w480 (Z_to_bv 64 (S + 43888)) w496 w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) (Z_to_bv 64 (18446744073709551615 - (S + 43888))) w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_L7C L d t mn mx ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_L7C F L d s t mn mx))
      (MS (mkR (Z_to_bv 64 0xb131c) (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (S + 45436 + 1032 * t)) (Z_to_bv 64 (S + 51628 + 1032 * t)) (Z_to_bv 64 (S + 57820 + 1032 * t)) (Z_to_bv 64 (S + 43888 + 258 * t)) (Z_to_bv 64 mn) (Z_to_bv 64 mx) (Z_to_bv 64 (sv_alphaSize L)) x17 (Z_to_bv 64 (S + 43888 + 258 * t)) (Z_to_bv 64 (S + 43888 + 258 * t)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 258) (Z_to_bv 64 2147450880) (Z_to_bv 64 mn) (Z_to_bv 64 t) (Z_to_bv 64 (sv_alphaSize L)) (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xa8eac) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_LZU (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (k : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x15 x16 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w80 : word)
         (w360 w376 w384 w400 w408 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 w528 w720 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d_set_unzftab d (clear256 (Z.to_nat k) 0 (d_unzftab d))) s) ->
    B0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 64012)) (Z_to_bv 64 (S + 57820)) (Z_to_bv 64 (S + 45436)) (Z_to_bv 64 (S + 51628)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3160)) w80 (Z_to_bv 64 (18446744073709551615 - (S + 64012))) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (18446744073709551615 - (S + 57820))) (Z_to_bv 64 (S + 2047)) ->
    B0FH A m (Z_to_bv 64 (100000 * d_bs100k d)) (Z_to_bv 64 (sv_alphaSize L - 1)) w360 (Z_to_bv 64 (sv_nSelectors L)) w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 (Z_to_bv 64 (18446744073709551615 - (S + 51628))) (Z_to_bv 64 (18446744073709551615 - (S + 45436))) w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_H7M L d ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_H7M F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 (Z_to_bv 64 (4 * k)) (Z_to_bv 64 (S + 68)) (Z_to_bv 64 (18446744073709551615 - (S + 68))) (Z_to_bv 64 1024) x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb13dc) (a_fc A) None m (seg_rom b0segs)).

End ACeilS1.
