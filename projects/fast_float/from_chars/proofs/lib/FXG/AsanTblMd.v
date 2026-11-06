(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxImg FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require Import AsanTblAll AsanTblM.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition IMGMd_c : tree Z := mk_img_runsM S0M_WR TEmpty.
Definition TBLMd : tree xi := TBLM.
Definition IMGMd : tree Z := IMGM.
Lemma IMGMd_eq : IMGMd = IMGMd_c. Proof. vm_cast_no_check (@eq_refl (tree Z) IMGM). Qed.
Lemma TBLMd_ok : tbl_ok ASEGS TBLMd. Proof. exact TBLA_ok. Qed.       (* [comment removed for export] *)
Lemma TBLMd_ecall : ecall_ok ASEGS TBLMd. Proof. exact TBLA_ecall. Qed.
Lemma mk_img_runsM_ok : forall rs t, Forall (fun p => 0 <= fst p) rs -> img_ok ASEGS t -> img_ok ASEGS (mk_img_runsM rs t).
Proof.
  induction rs as [|[lo n] rs IH]; intros t Hrs Ht; cbn [mk_img_runsM]; [exact Ht|].
  inversion Hrs as [|? ? Hp Hrs']; subst. apply IH; [exact Hrs'|]. apply mk_img_acc_ok; [|exact Ht].
  cbn [fst] in Hp. apply Z.shiftr_nonneg. exact Hp.
Qed.
Lemma IMGMd_ok : img_ok ASEGS IMGMd.
Proof.
  rewrite IMGMd_eq. apply mk_img_runsM_ok; [|intros p w Hp; rewrite tget_empty in Hp; discriminate].
  assert (H : forallb (fun p => Z.leb 0 (fst p)) S0M_WR = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. rewrite Forall_forall. intros p Hp. apply Z.leb_le. exact (H p Hp).
Qed.
