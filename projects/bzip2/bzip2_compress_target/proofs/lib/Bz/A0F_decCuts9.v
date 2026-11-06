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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU9 DecCutFA A0F_decV.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Export A0F_decRet.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition A0F_cut_L9S (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (uc E j : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x6 x7 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w48 w80 : word)
         (w496 w544 w552 w600 w608 w632 w640 w656 w664 w680 w696 w704 w712 w720 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    A0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 2124)) w48 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 (S + 8)) w80 (Z_to_bv 64 (S + 7820)) ->
    A0FH A m w496 (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (S + 57820 + 1032 * sv_gSel L)) (Z_to_bv 64 (S + 51628 + 1032 * sv_gSel L)) w544 w552 (Z_to_bv 64 (a_shs A)) (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 (sv_nextSym L)) (Z_to_bv 64 (sv_nSelectors L)) (Z_to_bv 64 (sv_groupPos L)) w600 w608 (Z_to_bv 64 (sv_nGroups L)) (Z_to_bv 64 (S + 45436 + 1032 * sv_gSel L)) w632 w640 (Z_to_bv 64 (sv_nblock L + j)) w656 w664 (Z_to_bv 64 (a_fb A)) w680 (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    aframe A m ->
    stk a0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono a0segs (a_m0 A) m -> mem_inv a0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_L9 L d uc E j ->
    b_small cx = 1%Z ->
    fuel_ok F (d) s ->
    evt a0segs (Q (K_L9 F L d s uc (sv_nblock L + j) (E - j)))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) (Z_to_bv 64 1) x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (-4)) (Z_to_bv 64 (S + 3160)) (Z_to_bv 64 (E - j)) (Z_to_bv 64 uc) (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_nblockMAX L - (sv_nblock L + j))) (Z_to_bv 64 (2 * (sv_nblock L + j))) (Z_to_bv 64 (a_shs A + 395)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) (Z_to_bv 64 (S + 7820)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xa837c) (a_fc A) None m (seg_rom a0segs)).

(* [comment removed for export] *)
Definition A0F_cut_L9F (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (uc E j : Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x6 x7 x11 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w48 w80 : word)
         (w496 w544 w552 w600 w608 w632 w640 w656 w664 w680 w696 w704 w712 w720 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    A0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 2124)) w48 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 (S + 8)) w80 (Z_to_bv 64 (S + 7820)) ->
    A0FH A m w496 (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 (sv_groupNo L)) (Z_to_bv 64 (S + 57820 + 1032 * sv_gSel L)) (Z_to_bv 64 (S + 51628 + 1032 * sv_gSel L)) w544 w552 (Z_to_bv 64 (a_shs A)) (Z_to_bv 64 (sv_gMinlen L)) (Z_to_bv 64 (sv_nextSym L)) (Z_to_bv 64 (sv_nSelectors L)) (Z_to_bv 64 (sv_groupPos L)) w600 w608 (Z_to_bv 64 (sv_nGroups L)) (Z_to_bv 64 (S + 45436 + 1032 * sv_gSel L)) w632 w640 (Z_to_bv 64 (sv_nblock L + j)) w656 w664 (Z_to_bv 64 (a_fb A)) w680 (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    aframe A m ->
    stk a0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono a0segs (a_m0 A) m -> mem_inv a0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    dinv_L9 L d uc E j ->
    b_small cx = 0%Z ->
    fuel_ok F (d) s ->
    evt a0segs (Q (K_L9 F L d s uc (sv_nblock L + j) (E - j)))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) (Z_to_bv 64 1) x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (-4)) x11 (Z_to_bv 64 (E - j)) (Z_to_bv 64 uc) (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_nblockMAX L - (sv_nblock L + j))) (Z_to_bv 64 (4 * (sv_nblock L + j))) (Z_to_bv 64 (a_shs A + 394)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) (Z_to_bv 64 (S + 7820)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xa8414) (a_fc A) None m (seg_rom a0segs)).

End ACeilS1.
