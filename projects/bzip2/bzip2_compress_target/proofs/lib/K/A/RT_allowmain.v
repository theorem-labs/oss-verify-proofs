(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Mem Frame Cells Step Arr ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface RT_state.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Mem Frame Cells Step Arr ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_state.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma A_bytes_allow_main : forall L, layout_ok L -> A_bytes (allow_main L) <= 2 ^ 35.
Proof.
  intros L HL. unfold layout_ok in HL.
  destruct HL as ((Hlo & Hhi) & _ & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & _ & _ & _ & _ & _ & (F1 & F2 & F3 & F4 & F5) & _ & (S1 & S2 & S3 & S4 & S5) & _).
  unfold allow_main, A_bytes, pg_up, pg_dn, shad, SHB, l_ACEIL, STACK_WIN, SEGTOP_A, sp_window_lo, sp_window_hi in *. cbn [fst snd].
  unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Mem Frame Cells Step Arr ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow RT_iface RT_state.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma A_bytes_allow_main : forall L, layout_ok L -> A_bytes (allow_main L) <= 2 ^ 35.
Proof.
  intros L HL. unfold layout_ok in HL.
  destruct HL as ((Hlo & Hhi) & _ & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & _ & _ & _ & _ & _ & (F1 & F2 & F3 & F4 & F5) & _ & (S1 & S2 & S3 & S4 & S5) & _).
  unfold allow_main, A_bytes, pg_up, pg_dn, shad, SHB, l_ACEIL, STACK_WIN, SEGTOP_A, sp_window_lo, sp_window_hi in *. cbn [fst snd].
  unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
