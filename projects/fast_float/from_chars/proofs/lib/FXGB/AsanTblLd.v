(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxImg FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require Import AsanTblAll AsanTblM AsanTblMd AsanTblL.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition TBLLd : tree xi := TBLA.       (* [comment removed for export] *)
Definition IMGLd : tree Z := mk_img_runsM (S0M_WR ++ S0L_WR) TEmpty.
Lemma TBLLd_ok : tbl_ok ASEGS TBLLd. Proof. exact TBLA_ok. Qed.
Lemma TBLLd_ecall : ecall_ok ASEGS TBLLd. Proof. exact TBLA_ecall. Qed.
Lemma IMGLd_ok : img_ok ASEGS IMGLd.
Proof.
  apply mk_img_runsM_ok; [|intros p w Hp; rewrite tget_empty in Hp; discriminate].
  assert (H : forallb (fun p => Z.leb 0 (fst p)) (S0M_WR ++ S0L_WR) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. rewrite Forall_forall. intros p Hp. apply Z.leb_le. exact (H p Hp).
Qed.
(* [comment removed for export] *)
