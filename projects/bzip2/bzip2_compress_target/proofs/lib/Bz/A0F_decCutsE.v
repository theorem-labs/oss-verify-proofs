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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU11 DecCutFA A0F_decV.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU11 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Export A0F_decRet.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition A0F_cut_L21 (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (i : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x14 x15 x16 x17 x18 x22 x24 x26 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w48 w80 w88 : word)
         (w496 w504 w512 w520 w528 w536 w544 w552 w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 w656 w664 w696 w704 w712 w720 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    A0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 2124)) w48 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 (S + 8)) w80 w88 ->
    A0FH A m w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 (Z_to_bv 64 (sv_nblock L)) w656 w664 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 i) (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    aframe A m ->
    stk a0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono a0segs (a_m0 A) m -> mem_inv a0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_L21 L d i ->
    fuel_ok F (d) s ->
    evt a0segs (Q (K_L21 F L d s i))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (-4)) (Z_to_bv 64 (S + 68 + 4 * i)) (Z_to_bv 64 (S + 68 + 4 * i)) (Z_to_bv 64 (256 - i)) x14 x15 x16 x17 x18 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) x22 (Z_to_bv 64 (S + 56)) x24 (Z_to_bv 64 (a_shs A + 7)) x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xa689c) (a_fc A) None m (seg_rom a0segs)).

(* [comment removed for export] *)
Definition A0F_cut_L22 (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (k : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x12 x16 x17 x22 x24 x26 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w48 w80 w88 : word)
         (w496 w504 w512 w520 w528 w536 w544 w552 w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 w656 w664 w680 w696 w704 w712 w720 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    A0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 2124)) w48 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 (S + 8)) w80 w88 ->
    A0FH A m w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 (Z_to_bv 64 (sv_nblock L)) w656 w664 (Z_to_bv 64 (a_fb A)) w680 (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    aframe A m ->
    stk a0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono a0segs (a_m0 A) m -> mem_inv a0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_L22 L d (k + 1) ->
    fuel_ok F (d) s ->
    evt a0segs (Q (K_L22 F L d s (k + 1)))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (-4)) (Z_to_bv 64 (S + 1100 + 4 * k)) x12 (Z_to_bv 64 (a_shs A + 137)) (Z_to_bv 64 (S + 1100 + 4 * k)) (Z_to_bv 64 (256 - k)) x16 x17 (Z_to_bv 64 (S + 1096)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) x22 (Z_to_bv 64 (S + 56)) x24 (Z_to_bv 64 (a_shs A + 7)) x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xa691c) (a_fc A) None m (seg_rom a0segs)).

(* [comment removed for export] *)
Definition A0F_cut_L23 (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (k : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x15 x16 x17 x22 x24 x26 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w48 w80 w88 : word)
         (w496 w504 w512 w520 w528 w536 w544 w552 w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 w656 w664 w680 w696 w704 w712 w720 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    A0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 2124)) w48 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 (S + 8)) w80 w88 ->
    A0FH A m w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 (Z_to_bv 64 (sv_nblock L)) w656 w664 (Z_to_bv 64 (a_fb A)) w680 (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    aframe A m ->
    stk a0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono a0segs (a_m0 A) m -> mem_inv a0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_L23 L d (k + 1) ->
    fuel_ok F (d) s ->
    evt a0segs (Q (K_L23 F L d s (k + 1)))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (-4)) (Z_to_bv 64 (S + 1100 + 4 * k)) (Z_to_bv 64 (psum (zget (d_unzftab d)) k)) (Z_to_bv 64 (S + 1100 + 4 * k)) (Z_to_bv 64 (256 - k)) x15 x16 x17 (Z_to_bv 64 (S + 1096)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) x22 (Z_to_bv 64 (S + 56)) x24 (Z_to_bv 64 (a_shs A + 7)) x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xa6998) (a_fc A) None m (seg_rom a0segs)).

(* [comment removed for export] *)
Definition A0F_cut_L24 (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (i : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x14 x15 x16 x17 x22 x24 x26 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w48 w80 w88 : word)
         (w496 w504 w512 w520 w528 w536 w544 w552 w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 w656 w664 w696 w704 w712 w720 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    A0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 2124)) w48 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 (S + 8)) w80 w88 ->
    A0FH A m w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 (Z_to_bv 64 (sv_nblock L)) w656 w664 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 i) (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    aframe A m ->
    stk a0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono a0segs (a_m0 A) m -> mem_inv a0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_L24 L d i ->
    fuel_ok F (d) s ->
    evt a0segs (Q (K_L24 F L d s i))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (-4)) (Z_to_bv 64 (S + 1096 + 4 * i)) (Z_to_bv 64 (257 - i)) (Z_to_bv 64 (S + 1096 + 4 * i)) x14 x15 x16 x17 (Z_to_bv 64 (S + 1096)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) x22 (Z_to_bv 64 (S + 56)) x24 (Z_to_bv 64 (a_shs A + 7)) x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xa69ec) (a_fc A) None m (seg_rom a0segs)).

(* [comment removed for export] *)
Definition A0F_cut_L25 (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (i : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x14 x15 x16 x17 x22 x24 x26 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w48 w80 w88 : word)
         (w496 w504 w512 w520 w528 w536 w544 w552 w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 w656 w664 w696 w704 w712 w720 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    A0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 2124)) w48 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 (S + 8)) w80 w88 ->
    A0FH A m w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 (Z_to_bv 64 (sv_nblock L)) w656 w664 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 i) (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    aframe A m ->
    stk a0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono a0segs (a_m0 A) m -> mem_inv a0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_L25 L d i ->
    fuel_ok F (d) s ->
    evt a0segs (Q (K_L25 F L d s i))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (-4)) (Z_to_bv 64 (S + 1096 + 4 * (i - 1))) (Z_to_bv 64 (S + 1096 + 4 * i)) (Z_to_bv 64 (257 - i)) x14 x15 x16 x17 (Z_to_bv 64 (S + 1096)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) x22 (Z_to_bv 64 (S + 56)) x24 (Z_to_bv 64 (a_shs A + 7)) x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xa6a54) (a_fc A) None m (seg_rom a0segs)).

(* [comment removed for export] *)
Definition A0F_cut_T (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x24 x26 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w48 w80 w88 : word)
         (w496 w504 w512 w520 w528 w536 w544 w552 w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 w656 w664 w680 w696 w704 w712 w720 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    A0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 2124)) w48 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 (S + 8)) w80 w88 ->
    A0FH A m w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 (Z_to_bv 64 (sv_nblock L)) w656 w664 (Z_to_bv 64 (a_fb A)) w680 (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    aframe A m ->
    stk a0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono a0segs (a_m0 A) m -> mem_inv a0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_T L d ->
    fuel_ok F (d) s ->
    evt a0segs (Q (K_T F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (S + 1096)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) x22 (Z_to_bv 64 (S + 56)) x24 (Z_to_bv 64 (a_shs A + 7)) x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xa6ac8) (a_fc A) None m (seg_rom a0segs)).

(* [comment removed for export] *)
Definition A0F_cut_HFAST (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x24 x26 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w48 w80 w88 : word)
         (w496 w504 w512 w520 w528 w536 w544 w552 w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 w656 w664 w680 w696 w704 w712 w720 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    A0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 2124)) w48 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 (S + 8)) w80 w88 ->
    A0FH A m w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 (Z_to_bv 64 (sv_nblock L)) w656 w664 (Z_to_bv 64 (a_fb A)) w680 (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    aframe A m ->
    stk a0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono a0segs (a_m0 A) m -> mem_inv a0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_HFAST L d ->
    fuel_ok F (d) s ->
    evt a0segs (Q (K_HFAST F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (S + 1096)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) x22 (Z_to_bv 64 (S + 56)) x24 (Z_to_bv 64 (a_shs A + 7)) x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xa70e0) (a_fc A) None m (seg_rom a0segs)).

(* [comment removed for export] *)
Definition A0F_cut_HSMALL (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x24 x26 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w48 w80 w88 : word)
         (w496 w504 w512 w520 w528 w536 w544 w552 w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 w656 w664 w680 w696 w704 w712 w720 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    A0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 2124)) w48 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 (S + 8)) w80 w88 ->
    A0FH A m w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 (Z_to_bv 64 (sv_nblock L)) w656 w664 (Z_to_bv 64 (a_fb A)) w680 (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    aframe A m ->
    stk a0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono a0segs (a_m0 A) m -> mem_inv a0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_HSMALL L d ->
    fuel_ok F (d) s ->
    evt a0segs (Q (K_HSMALL F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (S + 1096)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) x22 (Z_to_bv 64 (S + 56)) x24 (Z_to_bv 64 (a_shs A + 7)) x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xa6b64) (a_fc A) None m (seg_rom a0segs)).

End ACeilS1.
