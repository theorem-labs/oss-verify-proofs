(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzInv BzTables BzContracts.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDU6 BzDU7 DecCutFA A0F_decV.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU6 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU7 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Export A0F_decRet.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition A0F_cut_L7T (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (t : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w80 : word)
         (w496 w504 w512 w520 w528 w536 w544 w552 w568 w576 w608 w624 w632 w640 w656 w664 w696 w704 w712 w720 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    A0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 3192)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 (S + 8)) w80 (Z_to_bv 64 (S + 7820)) ->
    A0FH A m w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 (Z_to_bv 64 (S + 64012)) (Z_to_bv 64 (S + 57820)) (Z_to_bv 64 (sv_alphaSize L)) w608 (Z_to_bv 64 (sv_nGroups L)) w624 w632 w640 (Z_to_bv 64 (S + 51628)) w656 w664 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 45436)) (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    aframe A m ->
    stk a0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono a0segs (a_m0 A) m -> mem_inv a0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    (dinv_L7T L d t /\ (t < sv_nGroups L)%Z) ->
    fuel_ok F (d) s ->
    evt a0segs (Q (K_L7T F L d s t))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sv_alphaSize L)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) x22 (Z_to_bv 64 (S + 43888)) (Z_to_bv 64 t) (Z_to_bv 64 (S + 43888 + 258 * t)) (Z_to_bv 64 (S + 43888 + 258 * t)) (Z_to_bv 64 (sv_nSelectors L)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xa5084) (a_fc A) None m (seg_rom a0segs)).

(* [comment removed for export] *)
Definition A0F_cut_L7I (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (t i mn mx : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x13 x14 x16 x17 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w80 : word)
         (w496 w504 w512 w520 w528 w536 w544 w552 w568 w576 w608 w624 w632 w640 w656 w664 w696 w704 w712 w720 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    A0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 3192)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 (S + 8)) w80 (Z_to_bv 64 (S + 7820)) ->
    A0FH A m w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 (Z_to_bv 64 (S + 64012)) (Z_to_bv 64 (S + 57820)) (Z_to_bv 64 (sv_alphaSize L)) w608 (Z_to_bv 64 (sv_nGroups L)) w624 w632 w640 (Z_to_bv 64 (S + 51628)) w656 w664 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 45436)) (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    aframe A m ->
    stk a0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono a0segs (a_m0 A) m -> mem_inv a0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    (dinv_L7I L d t i mn mx /\ (i < sv_alphaSize L)%Z) ->
    fuel_ok F (d) s ->
    evt a0segs (Q (K_L7I F L d s t i mn mx))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (S + 43888 + 258 * t + i)) (Z_to_bv 64 (sv_alphaSize L - i)) (Z_to_bv 64 (S + 43888 + 258 * t + i)) x13 x14 (Z_to_bv 64 mx) x16 x17 (Z_to_bv 64 (sv_alphaSize L)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) (Z_to_bv 64 mn) (Z_to_bv 64 (S + 43888)) (Z_to_bv 64 t) (Z_to_bv 64 (S + 43888 + 258 * t)) (Z_to_bv 64 (S + 43888 + 258 * t)) (Z_to_bv 64 (sv_nSelectors L)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xa50a0) (a_fc A) None m (seg_rom a0segs)).

(* [comment removed for export] *)
Definition A0F_cut_L7C (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (t mn mx : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x16 x17 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w80 : word)
         (w496 w504 w512 w520 w528 w536 w544 w552 w568 w576 w608 w624 w632 w640 w656 w664 w696 w704 w712 w720 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    A0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 3192)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 (S + 8)) w80 (Z_to_bv 64 (S + 7820)) ->
    A0FH A m w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 (Z_to_bv 64 (S + 64012)) (Z_to_bv 64 (S + 57820)) (Z_to_bv 64 (sv_alphaSize L)) w608 (Z_to_bv 64 (sv_nGroups L)) w624 w632 w640 (Z_to_bv 64 (S + 51628)) w656 w664 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 45436)) (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    aframe A m ->
    stk a0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono a0segs (a_m0 A) m -> mem_inv a0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_L7C L d t mn mx ->
    fuel_ok F (d) s ->
    evt a0segs (Q (K_L7C F L d s t mn mx))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 (Z_to_bv 64 mx) x16 x17 (Z_to_bv 64 (sv_alphaSize L)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) (Z_to_bv 64 mn) (Z_to_bv 64 (S + 43888)) (Z_to_bv 64 t) (Z_to_bv 64 (S + 43888 + 258 * t)) (Z_to_bv 64 (S + 43888 + 258 * t)) (Z_to_bv 64 (sv_nSelectors L)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xa50ec) (a_fc A) None m (seg_rom a0segs)).

(* [comment removed for export] *)
Definition A0F_call_HBC (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (t mn mx : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x5 x6 x7 x17 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w80 : word)
         (w496 w504 w512 w520 w528 w536 w544 w552 w568 w576 w608 w624 w632 w640 w656 w664 w696 w704 w712 w720 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    A0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 3192)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 (S + 8)) w80 (Z_to_bv 64 (S + 7820)) ->
    A0FH A m w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 (Z_to_bv 64 (S + 64012)) (Z_to_bv 64 (S + 57820)) (Z_to_bv 64 (sv_alphaSize L)) w608 (Z_to_bv 64 (sv_nGroups L)) w624 w632 w640 (Z_to_bv 64 (S + 51628)) w656 w664 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 45436)) (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    aframe A m ->
    stk a0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono a0segs (a_m0 A) m -> mem_inv a0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_L7C L d t mn mx ->
    fuel_ok F (d) s ->
    evt a0segs (Q (K_L7C F L d s t mn mx))
      (MS (mkR (Z_to_bv 64 0xa5124) (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (S + 45436 + 1032 * t)) (Z_to_bv 64 (S + 51628 + 1032 * t)) (Z_to_bv 64 (S + 57820 + 1032 * t)) (Z_to_bv 64 (S + 43888 + 258 * t)) (Z_to_bv 64 mn) (Z_to_bv 64 mx) (Z_to_bv 64 (sv_alphaSize L)) x17 (Z_to_bv 64 (sv_alphaSize L)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) (Z_to_bv 64 mn) (Z_to_bv 64 (S + 43888)) (Z_to_bv 64 t) (Z_to_bv 64 (S + 43888 + 258 * t)) (Z_to_bv 64 (S + 43888 + 258 * t)) (Z_to_bv 64 (sv_nSelectors L)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x9dfd4) (a_fc A) None m (seg_rom a0segs)).

(* [comment removed for export] *)
Definition A0F_cut_HBCR (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (t mn mx : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w80 : word)
         (w496 w504 w512 w520 w528 w536 w544 w552 w568 w576 w608 w624 w632 w640 w656 w664 w696 w704 w712 w720 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (mt_rows t (sv_alphaSize L) d mn mx) s) ->
    A0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 3192)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 (S + 8)) w80 (Z_to_bv 64 (S + 7820)) ->
    A0FH A m w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 (Z_to_bv 64 (S + 64012)) (Z_to_bv 64 (S + 57820)) (Z_to_bv 64 (sv_alphaSize L)) w608 (Z_to_bv 64 (sv_nGroups L)) w624 w632 w640 (Z_to_bv 64 (S + 51628)) w656 w664 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 45436)) (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    aframe A m ->
    stk a0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono a0segs (a_m0 A) m -> mem_inv a0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_L7C L d t mn mx ->
    fuel_ok F (d) s ->
    evt a0segs (Q (K_L7C F L d s t mn mx))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sv_alphaSize L)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) (Z_to_bv 64 mn) (Z_to_bv 64 (S + 43888)) (Z_to_bv 64 t) (Z_to_bv 64 (S + 43888 + 258 * t)) (Z_to_bv 64 (S + 43888 + 258 * t)) (Z_to_bv 64 (sv_nSelectors L)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xa5124) (a_fc A) None m (seg_rom a0segs)).

(* [comment removed for export] *)
Definition A0F_cut_L7D (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (t : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w80 : word)
         (w496 w504 w512 w520 w528 w536 w544 w552 w568 w576 w608 w624 w632 w640 w656 w664 w696 w704 w712 w720 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    A0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 3192)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 (S + 8)) w80 (Z_to_bv 64 (S + 7820)) ->
    A0FH A m w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 (Z_to_bv 64 (S + 64012)) (Z_to_bv 64 (S + 57820)) (Z_to_bv 64 (sv_alphaSize L)) w608 (Z_to_bv 64 (sv_nGroups L)) w624 w632 w640 (Z_to_bv 64 (S + 51628)) w656 w664 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 45436)) (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    aframe A m ->
    stk a0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono a0segs (a_m0 A) m -> mem_inv a0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    (dinv_L7T L d (t + 1) /\ (0 <= t < sv_nGroups L)%Z) ->
    fuel_ok F (d) s ->
    evt a0segs (Q (K_L7T F L d s (t + 1)))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sv_alphaSize L)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) x22 (Z_to_bv 64 (S + 43888)) (Z_to_bv 64 (t + 1)) (Z_to_bv 64 (S + 43888 + 258 * t)) (Z_to_bv 64 (S + 43888 + 258 * t)) (Z_to_bv 64 (sv_nSelectors L)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xa5148) (a_fc A) None m (seg_rom a0segs)).

(* [comment removed for export] *)
Definition A0F_cut_H7M (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w48 w80 : word)
         (w496 w504 w512 w520 w528 w536 w544 w552 w568 w576 w584 w592 w608 w624 w632 w640 w648 w656 w664 w680 w696 w704 w712 w720 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    A0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 2124)) w48 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 (S + 8)) w80 (Z_to_bv 64 (S + 7820)) ->
    A0FH A m w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 w584 w592 (Z_to_bv 64 (sv_alphaSize L)) w608 (Z_to_bv 64 (sv_nGroups L)) w624 w632 w640 w648 w656 w664 (Z_to_bv 64 (a_fb A)) w680 (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    aframe A m ->
    stk a0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono a0segs (a_m0 A) m -> mem_inv a0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_H7M L d ->
    fuel_ok F (d) s ->
    evt a0segs (Q (K_H7M F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 (Z_to_bv 64 (S + 3192)) x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 (Z_to_bv 64 (sv_nSelectors L)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xa5180) (a_fc A) None m (seg_rom a0segs)).

(* [comment removed for export] *)
Definition A0F_call_MSU (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x5 x6 x7 x13 x14 x15 x16 x17 x23 x24 x25 x26 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w48 w80 : word)
         (w496 w504 w512 w520 w528 w536 w544 w552 w568 w576 w584 w592 w608 w624 w632 w640 w648 w656 w664 w680 w696 w704 w712 w720 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    A0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 2124)) w48 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 (S + 8)) w80 (Z_to_bv 64 (S + 7820)) ->
    A0FH A m w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 w584 w592 (Z_to_bv 64 (sv_alphaSize L)) w608 (Z_to_bv 64 (sv_nGroups L)) w624 w632 w640 w648 w656 w664 (Z_to_bv 64 (a_fb A)) w680 (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    aframe A m ->
    stk a0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono a0segs (a_m0 A) m -> mem_inv a0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_H7M L d ->
    fuel_ok F (d) s ->
    evt a0segs (Q (K_H7M F L d s))
      (MS (mkR (Z_to_bv 64 0xa51c0) (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (S + 68)) (Z_to_bv 64 0) (Z_to_bv 64 1024) x13 x14 x15 x16 x17 (Z_to_bv 64 (d_bs100k d)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) (Z_to_bv 64 (sv_alphaSize L - 2)) x23 x24 x25 x26 (Z_to_bv 64 (sv_nSelectors L)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x52ea0) (a_fc A) None m (seg_rom a0segs)).

(* [comment removed for export] *)
Definition A0F_cut_MSUR (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x26 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w48 w80 : word)
         (w496 w504 w512 w520 w528 w536 w544 w552 w568 w576 w584 w592 w608 w624 w632 w640 w648 w656 w664 w680 w696 w704 w712 w720 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d_set_unzftab d (clear256 256 0 (d_unzftab d))) s) ->
    A0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 2124)) w48 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 (S + 8)) w80 (Z_to_bv 64 (S + 7820)) ->
    A0FH A m w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 w584 w592 (Z_to_bv 64 (sv_alphaSize L)) w608 (Z_to_bv 64 (sv_nGroups L)) w624 w632 w640 w648 w656 w664 (Z_to_bv 64 (a_fb A)) w680 (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    aframe A m ->
    stk a0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono a0segs (a_m0 A) m -> mem_inv a0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_H7M L d ->
    fuel_ok F (d) s ->
    evt a0segs (Q (K_H7M F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (d_bs100k d)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) (Z_to_bv 64 (sv_alphaSize L - 2)) x23 x24 x25 x26 (Z_to_bv 64 (sv_nSelectors L)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xa51c0) (a_fc A) None m (seg_rom a0segs)).

(* [comment removed for export] *)
Definition A0F_cut_L7K (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (ii : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x6 x7 x10 x16 x17 x18 x23 x24 x25 x26 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w48 w80 : word)
         (w496 w512 w520 w528 w536 w544 w552 w568 w576 w584 w592 w608 w624 w632 w640 w648 w656 w664 w680 w696 w704 w712 w720 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    A0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 2124)) w48 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 (S + 8)) w80 (Z_to_bv 64 (S + 7820)) ->
    A0FH A m w496 (Z_to_bv 64 (100000 * d_bs100k d)) w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 w584 w592 (Z_to_bv 64 (sv_alphaSize L)) w608 (Z_to_bv 64 (sv_nGroups L)) w624 w632 w640 w648 w656 w664 (Z_to_bv 64 (a_fb A)) w680 (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    aframe A m ->
    stk a0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono a0segs (a_m0 A) m -> mem_inv a0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    (dinv_L7K L d ii /\ 0 <= ii)%Z ->
    fuel_ok F (d) s ->
    evt a0segs (Q (K_L7K F L d s ii))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) (Z_to_bv 64 ii) x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 (Z_to_bv 64 (S + 3724)) (Z_to_bv 64 15) (Z_to_bv 64 (16 * ii + 15)) (Z_to_bv 64 (3855 + 16 * ii)) (Z_to_bv 64 (S + 7820)) x16 x17 x18 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) (Z_to_bv 64 (sv_alphaSize L - 2)) x23 x24 x25 x26 (Z_to_bv 64 (sv_nSelectors L)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xa51f8) (a_fc A) None m (seg_rom a0segs)).

(* [comment removed for export] *)
Definition A0F_cut_L7J (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (ii dd : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x18 x23 x24 x25 x26 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w48 w80 : word)
         (w496 w512 w520 w528 w536 w544 w552 w568 w576 w584 w592 w608 w624 w632 w640 w648 w656 w664 w680 w696 w704 w712 w720 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    A0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 2124)) w48 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 (S + 8)) w80 (Z_to_bv 64 (S + 7820)) ->
    A0FH A m w496 (Z_to_bv 64 (100000 * d_bs100k d)) w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 w584 w592 (Z_to_bv 64 (sv_alphaSize L)) w608 (Z_to_bv 64 (sv_nGroups L)) w624 w632 w640 w648 w656 w664 (Z_to_bv 64 (a_fb A)) w680 (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    aframe A m ->
    stk a0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono a0segs (a_m0 A) m -> mem_inv a0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    (dinv_L7J L d ii dd /\ dd <= 15)%Z ->
    fuel_ok F (d) s ->
    evt a0segs (Q (K_L7J F L d s ii dd))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) (Z_to_bv 64 (dd - 1)) (Z_to_bv 64 (S + 3724 + 3855 + 16 * ii - dd)) (Z_to_bv 64 (16 * ii + 15 - dd)) (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (S + 3724 + 3855 + 16 * ii - dd)) (Z_to_bv 64 (S + 3724)) (Z_to_bv 64 15) (Z_to_bv 64 (16 * ii + 15)) (Z_to_bv 64 (3855 + 16 * ii - dd)) (Z_to_bv 64 (S + 7820)) (Z_to_bv 64 ii) (Z_to_bv 64 (3855 + 16 * ii)) x18 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) (Z_to_bv 64 (sv_alphaSize L - 2)) x23 x24 x25 x26 (Z_to_bv 64 (sv_nSelectors L)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xa5210) (a_fc A) None m (seg_rom a0segs)).

(* [comment removed for export] *)
Definition A0F_cut_L7G (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x24 x25 x26 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w48 w80 : word)
         (w496 w512 w520 w528 w536 w544 w552 w568 w576 w584 w592 w608 w624 w632 w640 w648 w656 w664 w680 w696 w704 w712 w720 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    A0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 2124)) w48 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 (S + 8)) w80 (Z_to_bv 64 (S + 7820)) ->
    A0FH A m w496 (Z_to_bv 64 (100000 * d_bs100k d)) w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 w584 w592 (Z_to_bv 64 (sv_alphaSize L)) w608 (Z_to_bv 64 (sv_nGroups L)) w624 w632 w640 w648 w656 w664 (Z_to_bv 64 (a_fb A)) w680 (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    aframe A m ->
    stk a0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono a0segs (a_m0 A) m -> mem_inv a0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_L7G L d ->
    fuel_ok F (d) s ->
    evt a0segs (Q (K_L7G F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) (Z_to_bv 64 (sv_alphaSize L - 2)) x23 x24 x25 x26 (Z_to_bv 64 (sv_nSelectors L)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xa528c) (a_fc A) None m (seg_rom a0segs)).

End ACeilS1.
