(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout RT_iface D_defs D_kit I_read RT_liveprim RT_globals.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require L_libA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2 Require Import L2Kit L2Act L2StmtD A0_fs_L2f A0_sessK A0F_decK.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzTac BzTables CmpMem AsanKit AsanKit2 AsanCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzInv BzContracts.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState BzDBlock BzDK DecCutFA A0F_decV A0F_decRet A0F_decCuts4 A0F_decCuts7.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCuts4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCuts7.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).

(* [comment removed for export] *)
Definition dk_setm0 (A : act14) (m : mem) (F : bvmap 5 word) (fc : bv 32) : act14 :=
  ACT (a_ra A) (a_sp A) (a_gp A) (a_tp A) (a_s0 A) (a_s1 A) (a_s2 A) (a_s3 A) (a_s4 A) (a_s5 A) (a_s6 A) (a_s7 A) (a_s8 A) (a_s9 A) (a_s10 A) (a_s11 A)
      F fc m (a_cx A) (a_h0 A) (a_b0 A) (a_lo A) (a_g1 A) (a_sv A) (a_payload A) (a_P A) (a_fb A) (a_shs A) (a_sht A) (a_shf A).

Section DECL2a.
Context {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis MSET : memset_icontract RT e_asan_memset.
Variable A : act14.                                   (* [comment removed for export] *)
Variables (sp0 : Z) (fr : list (Z * nat)) (live0 Wc : list (Z * Z)).
Hypothesis G : act_geom RT (a_lo A) (a_P A) (a_usp A) sp0 true 0 (a_fb A) (a_shf A) 64 8 fr live0 Wc.
Variable mi : mem.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc. Hypothesis MST : mat_stable PMc.
Variable T : TSet.
Notation PRESI := (PRESI (a_usp A) fr live0 Wc mi).
Notation SOK Σ := (sig_ok RT sp0 true 0 (a_fb A) fr live0 Σ).
Notation S := (b_s (a_cx A)).

(* [comment removed for export] *)
Definition QL (Σ : rts RT) (R0 : dres) : dres -> machine_state -> Prop :=
  fun r ms => r = R0 -> forall c', ASTA RT Σ PMc (eq ms) c' -> realizes asegs c' T.

Lemma act_ok_setm0 : forall ihi A0 m F fc, act_ok ihi A0 -> act_ok ihi (dk_setm0 A0 m F fc).
Proof. intros ihi A0 m F fc H. destruct A0. exact H. Qed.

Hypothesis AOK : act_ok AIHI0 A.
Hypothesis ATP : a_tp A = Z_to_bv 64 0x5fc0d8.
Hypothesis ROOM : a_lo A + RT_STACK <= a_P A - 256.
(* [comment removed for export] *)
Hypothesis W14C : forall x, ~ KFrame.outside (W14 A) x ->
  (a_P A - 256 <= x < a_usp A) \/ (a_fb A <= x < a_fb A + 64 - 8) \/ (a_shf A <= x < a_shf A + 8) \/ ~ outside Wc x.
Hypothesis DSC : forall x, S <= x < S + 64144 -> ~ outside Wc x.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

End DECL2a.
