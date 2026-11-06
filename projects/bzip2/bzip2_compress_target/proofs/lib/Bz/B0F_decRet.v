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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK DecCutFB B0F_decV.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition B0F_RETC (A : act14) (Q : dres -> machine_state -> Prop) : Prop :=
  forall (rv : Z) (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x11 x14 x24 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 : word)
         (w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w496 w504 w520 w528 w712 w720 w728 w736 w744 w752 : word),
    let usp := bv_unsigned (a_sp A) in let S := b_s (a_cx A) in
    dmem DI_B0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ->
    B0FH A m w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 w712 w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    (0 <= sv_nblock L <= 900000)%Z -> dpost14 (d_set_sv d L) ->
    evt b0segs (Q (DRet rv L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) (Z_to_bv 64 (a_shs A + 8007)) (Z_to_bv 64 (a_shs A + 8007)) (Z_to_bv 64 (a_shs A + 8008)) (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 rv) x11 (Z_to_bv 64 (a_shs A + 8004)) (Z_to_bv 64 (a_shs A + 8005)) x14 (Z_to_bv 64 (a_shs A + 8005)) (Z_to_bv 64 (a_shs A + 8006)) (Z_to_bv 64 (a_shs A + 8006)) (Z_to_bv 64 (a_shs A + 8010)) (Z_to_bv 64 (a_shs A + 8011)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 (a_shs A + 8011)) (Z_to_bv 64 (a_shs A + 8012)) (Z_to_bv 64 (a_shs A + 8012)) x24 (Z_to_bv 64 (a_shs A + 8013)) (Z_to_bv 64 (a_shs A + 8013)) (Z_to_bv 64 (a_shf A)) (Z_to_bv 64 (a_shs A + 8008)) (Z_to_bv 64 (a_shs A + 8009)) (Z_to_bv 64 (a_shs A + 8009)) (Z_to_bv 64 (a_shs A + 8010)))
          (a_F A) (Z_to_bv 64 0xafbe0) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_RET (A : act14) (Q : dres -> machine_state -> Prop) : Prop :=
  forall (rv : Z) (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 : word)
         (w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w496 w504 w520 w528 w712 w720 w728 w736 w744 w752 : word),
    let usp := bv_unsigned (a_sp A) in let S := b_s (a_cx A) in
    dmem DI_B0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ->
    B0FH A m w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 w712 w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    (0 <= sv_nblock L <= 900000)%Z -> dpost14 (d_set_sv d L) ->
    evt b0segs (Q (DRet rv L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 rv) x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 x22 x23 x24 x25 x26 (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xafb90) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_RET_OK (A : act14) (Q : dres -> machine_state -> Prop) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 : word)
         (w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w496 w504 w520 w528 w712 w720 w728 w736 w744 w752 : word),
    let usp := bv_unsigned (a_sp A) in let S := b_s (a_cx A) in
    dmem DI_B0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ->
    B0FH A m w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 w712 w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    (0 <= sv_nblock L <= 900000)%Z -> dpost14 (d_set_sv d L) ->
    evt b0segs (Q (DRet BZ_OK L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 x22 x23 x24 x25 x26 (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xa9f7c) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_RET_DATA (A : act14) (Q : dres -> machine_state -> Prop) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 : word)
         (w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w496 w504 w520 w528 w712 w720 w728 w736 w744 w752 : word),
    let usp := bv_unsigned (a_sp A) in let S := b_s (a_cx A) in
    dmem DI_B0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ->
    B0FH A m w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 w712 w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    (0 <= sv_nblock L <= 900000)%Z -> dpost14 (d_set_sv d L) ->
    evt b0segs (Q (DRet BZ_DATA_ERROR L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 x22 x23 x24 x25 x26 (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xafb8c) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_FLAG (A : act14) (Q : dres -> machine_state -> Prop) : Prop :=
  forall (rv : Z) (L : dsv) (d : dst) (s : dstrm) (J : jk) (fl : Z)
         (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 : word)
         (w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 w512 w520 w528 w712 w720 w728 w736 w744 w752 : word)
         (zt : word) (ng : nat) (jg j24 pos j38 : list byte),
    let usp := bv_unsigned (a_sp A) in let S := b_s (a_cx A) in
    dmem DI_B0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J (d_set_sv d L) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ->
    B0FH A m w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 w512 w520 w528 w712 w720 w728 w736 w744 w752 ->
    (a_P A + 760 + Z.of_nat ng + 104 = usp)%Z -> (ng = 0 \/ ng = 16)%nat ->
    ro_cells b0segs m (a_fb A + 56) [C8 (Z_to_bv 64 fl)] ->
    rw_cells b0segs m (a_P A + 128) (FM_CELLS A zt) ->
    rw_cells b0segs m (a_P A + 760) (CB ng jg :: FT_REGS A) ->
    rw_cells b0segs m (a_fb A) [C8 (Z_to_bv 64 1172321806); C8 (Z_to_bv 64 132751); C8 (Z_to_bv 64 693392); CB 8 j24; CB 6 pos; CB 18 j38] ->
    rw_cells b0segs m (a_shf A) [C1 df5b; C1 df5b; C1 df5b; C1 df5b; C1 df5b; C1 df5b; C1 df5b; C1 df5b] ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J (d_set_sv d L) s ->
    dpost14 (d_set_sv d L) ->
    evt b0segs (Q (DRet rv L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 rv) (Z_to_bv 64 fl) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xafe0c) (a_fc A) None m (seg_rom b0segs)).

End ACeilS1.
