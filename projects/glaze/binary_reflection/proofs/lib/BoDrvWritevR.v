(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvWritevR. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvWritevR.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoStdioWrite_run2.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

#[local] Notation BSEGS := AsanUbsan.M.loaded_segments.

Theorem both_HW1 : forall (R : shape_rel BSEGS) (fx : FPState), @BoStdioWrite_run2.BoStdioDefs.HYP_writev1_wall_stmt fx R.
Proof.
  intros R fx H A F regs pc m model w fd iov b1 n1 bs1 K _ _ Hwf Hinv Hcov _ HF HE Hh Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Rs1 Av1 Av2 Hiok Hb1 Ht1 Ht30 HK Hk.
  exact (sr_writev1_wall_lazy BSEGS R H A F regs pc m model w fd iov b1 n1 bs1 K Hwf Hinv Hcov HF HE Hh Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Rs1 Av1 Av2 Hiok Hb1 Ht1 Ht30 HK Hk).
Qed.
Theorem both_HW2 : forall (R : shape_rel BSEGS) (fx : FPState), @BoStdioWrite_run2.BoStdioDefs.HYP_writev2_wall_stmt fx R.
Proof.
  intros R fx H A F regs pc m model w fd iov b1 n1 b2 n2 bs1 bs2 K _ _ Hwf Hinv Hcov _ HF HE Hh Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Av0 Av1 Av2 Hiok Hb1 Hb2 Ht1 Ht30 HK Hk.
  exact (sr_writev2_wall_lazy BSEGS R H A F regs pc m model w fd iov b1 n1 b2 n2 bs1 bs2 K Hwf Hinv Hcov HF HE Hh Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Av0 Av1 Av2 Hiok Hb1 Hb2 Ht1 Ht30 HK Hk).
Qed.
Theorem both_HW0 : forall (R : shape_rel BSEGS) (fx : FPState), @BoStdioWrite_run2.BoStdioDefs.HYP_writev1_zero_stmt fx R.
Proof.
  intros R fx H A F regs pc m model w fd iov b1 K _ _ Hwf Hinv Hcov _ HF HE Hh Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Av0 Hiok Hb1 Hc.
  exact (sr_writev1_zero_lazy BSEGS R H A F regs pc m model w fd iov b1 K Hwf Hinv Hcov HF HE Hh Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Av0 Hiok Hb1 Hc).
Qed.
