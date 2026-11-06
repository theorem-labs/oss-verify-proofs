(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts BzContracts0 DecCut DecAux.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecAuxM S0_dec_U13.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDefs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzInv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzContracts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzContracts0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac.DecAuxB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAuxM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_dec_U13.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Export S0_decCuts.
From Stdlib Require Lia. 
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
Module S0_decCutsB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDefs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzInv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzContracts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzContracts0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac.DecAuxB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_dec_U13.
Export OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_decCuts.
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Open Scope bv_scope.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

End ACeilS1.
End S0_decCutsB.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section ACeilS1. Context {ACEIL__ : ACeil}.


Definition tabs_upto (r : drest) (t alpha : Z) : Prop :=
  forall t', (0 <= t' < t)%Z -> exists mn, grp_tab r alpha t' mn.

Lemma tabs_upto_0 : forall r alpha, tabs_upto r 0 alpha.
Proof. intros r alpha t' H. exfalso. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition S0_cut_L7C (A : act14) (ng nsc alpha t mn mx : Z) : Prop :=
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x14 x16 x17 x23 x26 x27 x28 x29 x31 : word)
         (v : dv) (m : word -> option byte)
         (j0 : list byte) (f8 f16 f32 f40 f56 f64 f72 f80 f88 f136 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m v ->
    S0FR A m j0 f8 f16 (Z_to_bv 64 nsc) f32 f40 (Z_to_bv 64 (alpha + 43888)) f56 f64 f72 f80 f88 (Z_to_bv 64 ng)
         (Z_to_bv 64 (a_S A + 2124)) (Z_to_bv 64 (a_S A + 7884)) (Z_to_bv 64 (a_S A + 3152)) (Z_to_bv 64 (a_S A + 7820))
         f136 (Z_to_bv 64 (a_S A + 57820)) (Z_to_bv 64 (a_S A + 51628)) (Z_to_bv 64 (a_S A + 45436)) f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (a_usp A + -320) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpure (a_cx A) (a_h0 A) (a_b0 A) (a_payload A) v ->
    (in_bits (dv_b v) (dv_h v) < in_bits (a_b0 A) (a_h0 A))%Z ->
    sh_state (dv_h v) <> 2%Z ->
    (1 <= sm_nInUse (dv_d v) <= 256)%Z ->
    (2 <= ng <= 6)%Z -> (1 <= nsc <= 18002)%Z ->
    selm_ok (r_sel (dv_r v)) nsc ng ->
    (sm_nInUse (dv_d v) + 2)%Z = alpha -> (0 <= t < ng)%Z ->
    len_ok (r_len (dv_r v)) ng alpha ->
    tabs_upto (dv_r v) t alpha ->
    (1 <= mn /\ mn <= mx <= 20)%Z ->
    (forall j, (0 <= j < alpha)%Z -> (mn <= uv8 (r_len (dv_r v)) (258 * t + j) <= mx)%Z) ->
    evt s0segs (POST14 DI_S0 A)
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 (a_S A + 64036)) x9
              x10 x11 x12 (Z_to_bv 64 (258 * t)) x14 (Z_to_bv 64 mx) x16 x17 (Z_to_bv 64 mn) (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (a_S A + 43888)) (Z_to_bv 64 (a_S A + 64012))
              (Z_to_bv 64 (a_S A + 2047)) x23 (Z_to_bv 64 t) (Z_to_bv 64 (a_S A + 43888 + 258 * t)) x26 x27 x28 x29
              (Z_to_bv 64 alpha) x31)
          (a_F A) (Z_to_bv 64 0x1dd58) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition S0_cut_L7D (A : act14) (ng nsc alpha t : Z) : Prop :=
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x31 : word)
         (v : dv) (m : word -> option byte)
         (j0 : list byte) (f8 f16 f32 f40 f56 f64 f72 f80 f88 f136 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m v ->
    S0FR A m j0 f8 f16 (Z_to_bv 64 nsc) f32 f40 (Z_to_bv 64 (alpha + 43888)) f56 f64 f72 f80 f88 (Z_to_bv 64 ng)
         (Z_to_bv 64 (a_S A + 2124)) (Z_to_bv 64 (a_S A + 7884)) (Z_to_bv 64 (a_S A + 3152)) (Z_to_bv 64 (a_S A + 7820))
         f136 (Z_to_bv 64 (a_S A + 57820)) (Z_to_bv 64 (a_S A + 51628)) (Z_to_bv 64 (a_S A + 45436)) f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (a_usp A + -320) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpure (a_cx A) (a_h0 A) (a_b0 A) (a_payload A) v ->
    (in_bits (dv_b v) (dv_h v) < in_bits (a_b0 A) (a_h0 A))%Z ->
    sh_state (dv_h v) <> 2%Z ->
    (1 <= sm_nInUse (dv_d v) <= 256)%Z ->
    (2 <= ng <= 6)%Z -> (1 <= nsc <= 18002)%Z ->
    selm_ok (r_sel (dv_r v)) nsc ng ->
    (sm_nInUse (dv_d v) + 2)%Z = alpha -> (0 <= t < ng)%Z ->
    len_ok (r_len (dv_r v)) ng alpha ->
    tabs_upto (dv_r v) (t + 1) alpha ->
    evt s0segs (POST14 DI_S0 A)
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 (a_S A + 64036)) x9
              x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (a_S A)) (Z_to_bv 64 (a_S A + 43888)) (Z_to_bv 64 (a_S A + 64012))
              (Z_to_bv 64 (a_S A + 2047)) (Z_to_bv 64 alpha) (Z_to_bv 64 (t + 1)) (Z_to_bv 64 (a_S A + 43888 + 258 * t)) x26 x27 x28 x29
              (Z_to_bv 64 alpha) x31)
          (a_F A) (Z_to_bv 64 0x1dda0) (a_fc A) None m (seg_rom s0segs)).


(* [comment removed for export] *)
Definition S0_cut_L7G (A : act14) (ng nsc alpha : Z) : Prop :=
  forall (x1 x5 x6 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x24 x27 x28 x29 x30 x31 : word)
         (v : dv) (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m v ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96
         (Z_to_bv 64 (a_S A + 2124)) (Z_to_bv 64 (a_S A + 7884)) (Z_to_bv 64 (a_S A + 3152)) (Z_to_bv 64 (a_S A + 7820))
         f136 f144 f152 f160 f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (a_usp A + -320) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpure (a_cx A) (a_h0 A) (a_b0 A) (a_payload A) v ->
    (in_bits (dv_b v) (dv_h v) < in_bits (a_b0 A) (a_h0 A))%Z ->
    sh_state (dv_h v) <> 2%Z ->
    (1 <= sm_nInUse (dv_d v) <= 256)%Z ->
    (2 <= ng <= 6)%Z -> (1 <= nsc <= 18002)%Z ->
    selm_ok (r_sel (dv_r v)) nsc ng ->
    (sm_nInUse (dv_d v) + 2)%Z = alpha ->
    tabs_ok (dv_r v) ng alpha ->
    ag32s (r_unz (dv_r v)) (fun _ => 0%Z) 256 ->
    mtf_ok (dv_r v) (fun l => 3840 + 16 * l)%Z ->
    evt s0segs (POST14 DI_S0 A)
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -320)) (a_gp A) (a_tp A) x5 x6 (Z_to_bv 64 (100000 * b_n (a_cx A))) (Z_to_bv 64 (a_S A + 64036)) x9
              x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (a_S A)) x20 x21
              (Z_to_bv 64 (a_S A + 2047)) (Z_to_bv 64 alpha) x24 (Z_to_bv 64 nsc) (Z_to_bv 64 (alpha - 2)) x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1de7c) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

End ACeilS1.
