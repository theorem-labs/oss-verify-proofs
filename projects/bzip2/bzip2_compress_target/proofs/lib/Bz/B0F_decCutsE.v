(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU11 DecCutFB B0F_decV.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU11 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Export B0F_decRet.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition B0F_cut_L21 (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (i : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x11 x16 x17 x18 x19 x21 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w112 : word)
         (w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w496 w504 w520 w528 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 (Z_to_bv 64 (S + 3160)) w80 w88 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) w112 (Z_to_bv 64 (S + 2047)) ->
    B0FH A m w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 (Z_to_bv 64 (a_shs A + 1)) (Z_to_bv 64 i) w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_L21 L d i ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_L21 F L d s i))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (-4)) x11 (Z_to_bv 64 (18446744073709551615 - (S + 68))) (Z_to_bv 64 (4 * i)) (Z_to_bv 64 (S + 68)) (Z_to_bv 64 1024) x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) (Z_to_bv 64 (S + 56)) (Z_to_bv 64 (a_shs A + 7)) x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb3028) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_L22 (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (k : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x11 x14 x16 x17 x19 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w112 : word)
         (w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w496 w504 w520 w528 w720 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 (Z_to_bv 64 (S + 3160)) w80 w88 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) w112 (Z_to_bv 64 (S + 2047)) ->
    B0FH A m w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_L22 L d (k + 1) ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_L22 F L d s (k + 1)))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (-4)) x11 (Z_to_bv 64 (18446744073709551615 - (S + 68))) (Z_to_bv 64 1024) x14 (Z_to_bv 64 (4 * k)) x16 x17 (Z_to_bv 64 (S + 1096)) x19 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 (18446744073709551615 - (S + 1096))) (Z_to_bv 64 2147450880) (Z_to_bv 64 (S + 56)) (Z_to_bv 64 (a_shs A + 7)) x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb30b4) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_L23 (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (k : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x16 x17 x19 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w112 : word)
         (w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w496 w504 w520 w528 w720 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 (Z_to_bv 64 (S + 3160)) w80 w88 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) w112 (Z_to_bv 64 (S + 2047)) ->
    B0FH A m w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_L23 L d (k + 1) ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_L23 F L d s (k + 1)))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (-4)) (Z_to_bv 64 (S + 1100 + 4 * k)) (Z_to_bv 64 (S + 1096 + 4 * k)) (Z_to_bv 64 (4 * k + 4)) (Z_to_bv 64 (256 - k)) (Z_to_bv 64 (S + 4 * k)) x16 x17 (Z_to_bv 64 (S + 1096)) x19 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 (18446744073709551615 - (S + 1096))) (Z_to_bv 64 2147450880) (Z_to_bv 64 (S + 56)) (Z_to_bv 64 (a_shs A + 7)) x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb3138) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_L24 (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (i : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x11 x14 x15 x16 x17 x19 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w112 : word)
         (w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w496 w504 w520 w528 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 (Z_to_bv 64 (S + 3160)) w80 w88 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) w112 (Z_to_bv 64 (S + 2047)) ->
    B0FH A m w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 (Z_to_bv 64 (a_shs A + 1)) (Z_to_bv 64 i) w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_L24 L d i ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_L24 F L d s i))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (-4)) x11 (Z_to_bv 64 (4 * i)) (Z_to_bv 64 1028) x14 x15 x16 x17 (Z_to_bv 64 (S + 1096)) x19 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 (18446744073709551615 - (S + 1096))) (Z_to_bv 64 2147450880) (Z_to_bv 64 (S + 56)) (Z_to_bv 64 (a_shs A + 7)) x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb31d8) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_L25 (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (i : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x16 x17 x19 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w112 : word)
         (w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w496 w504 w520 w528 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 (Z_to_bv 64 (S + 3160)) w80 w88 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) w112 (Z_to_bv 64 (S + 2047)) ->
    B0FH A m w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 (Z_to_bv 64 (a_shs A + 1)) (Z_to_bv 64 i) w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_L25 L d i ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_L25 F L d s i))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (-4)) (Z_to_bv 64 (S + 1096 + 4 * i)) (Z_to_bv 64 (S + 1096 + 4 * (i - 1))) (Z_to_bv 64 (4 * i)) (Z_to_bv 64 (257 - i)) (Z_to_bv 64 (S + 4 * (i - 1))) x16 x17 (Z_to_bv 64 (S + 1096)) x19 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 (18446744073709551615 - (S + 1096))) (Z_to_bv 64 2147450880) (Z_to_bv 64 (S + 56)) (Z_to_bv 64 (a_shs A + 7)) x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb3258) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_T (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w112 : word)
         (w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w496 w504 w520 w528 w720 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 (Z_to_bv 64 (S + 3160)) w80 w88 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) w112 (Z_to_bv 64 (S + 2047)) ->
    B0FH A m w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_T L d ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_T F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (S + 1096)) x19 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 (18446744073709551615 - (S + 1096))) (Z_to_bv 64 2147450880) (Z_to_bv 64 (S + 56)) (Z_to_bv 64 (a_shs A + 7)) x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb32d4) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_HFAST (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w104 w112 w120 : word)
         (w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w496 w504 w520 w528 w712 w720 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 (Z_to_bv 64 (S + 3152)) w104 w112 w120 ->
    B0FH A m w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 w712 w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_HFAST L d ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_HFAST F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (S + 1096)) x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) (Z_to_bv 64 (S + 56)) (Z_to_bv 64 (a_shs A + 7)) x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb3bf4) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_HSMALL (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w104 w112 : word)
         (w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w496 w504 w520 w528 w712 w720 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 (Z_to_bv 64 (S + 3160)) w80 w88 (Z_to_bv 64 (S + 3152)) w104 w112 (Z_to_bv 64 (S + 2047)) ->
    B0FH A m w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 w712 w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_HSMALL L d ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_HSMALL F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (S + 1096)) x19 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 (18446744073709551615 - (S + 1096))) (Z_to_bv 64 2147450880) (Z_to_bv 64 (S + 56)) (Z_to_bv 64 (a_shs A + 7)) x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb3388) (a_fc A) None m (seg_rom b0segs)).

End ACeilS1.
