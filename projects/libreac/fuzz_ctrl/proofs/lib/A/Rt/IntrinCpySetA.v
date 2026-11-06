(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* lib/A/Rt/IntrinCpySetA.v -- image A (asan) of libreac/fuzz_ctrl: the core's memory-intrinsic contract
   Reusable.YG0d.aintrin_realizes at A's RAW __asan_memcpy entry 0x52028 (OCpy) and __asan_memset entry 0x524c4
   (OSet), stated with exactly the terms of the binders AMEMCPY / AMEMSET of
   lib/A/Prog/C_reac_box_model_block.v pb_reac_box_model_block_stmt (:189-190 at 4f23eb39c50):
     (AMEMSET : aintrin_realizes SEGS B OSet (SIGMA GS___asan_memset))
     (AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA GS___asan_memcpy))
   with SEGS := AB1v.tfibsegs and SIGMA := @pa_sigma _ ctrl_listing CtrlImg.PI_ctrl (that file's Section d
   Notations).  One writer: a Theorem Labs lane.
   rule 24: no function is proved here; this file only restates the image-A core's proved theorems
   lib/A/AE2q.v asan_memcpy_realizes and lib/A/AE2r.v asan_memset_realizes in the binder form.

   WHAT THIS FILE PROVES (Section IntrinA):
     asan_memcpy_aintrin / asan_memset_aintrin   for every B with A.AF0m.CtrlTSyms B (stage form);
     ctrlA_asan_memcpy_realizes / ctrlA_asan_memset_realizes   at B := A.AD2l.CtrlB (the top's instance).
   AR_laws by the core's Reusable.YG0q.AR_laws_ok; CtrlTSyms CtrlB by A.AD2l.CtrlB_syms.

   WHY THE RAW ENTRIES.  SIGMA GS___asan_memcpy reduces to CtrlAddr.ctrl_sigma GS___asan_memcpy = 0x52028 and
   SIGMA GS___asan_memset to 0x524c4 (CtrlImg.v:87 pa_sigma := ctrl_sigma; CtrlAddr.v ctrl_sigma), which are
   A.AB1w.tfib_A_asan_memcpy / tfib_A_asan_memset and the ELF symbols __asan_memcpy / __asan_memset of the pinned
   fuzz_ctrl.asan.  The core's interceptor lemmas A/AD1o.v ocpy_of_icpt / oset_of_icpt are stated at
   pc_wrap_memcpy / pc_wrap_memset = 0x52024 / 0x52020 (A/AF0l.v:14), the trampolines, so they do not fit.

   No lib/B file is in the closure: the Requires below name lib/Reusable and lib/A modules only. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YG0f YG0d YG0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v AF0m AD2l AE2q AE2r.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require CtrlSyms CtrlList CtrlPa CtrlImg.
Local Open Scope Z_scope.

Section IntrinA.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
        {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}.

(* the binder file's Section d Notations (here abbreviations), with every name written in full *)
#[local] Abbreviation SEGS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AB1v.tfibsegs.
#[local] Abbreviation SIGMA := (@OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.CtrlPa.pa_sigma _
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.CtrlList.ctrl_listing
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.CtrlImg.PI_ctrl).
#[local] Abbreviation aintrin_realizes := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.aintrin_realizes.
#[local] Abbreviation OCpy := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.OCpy.
#[local] Abbreviation OSet := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.OSet.
#[local] Abbreviation GS___asan_memcpy := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.CtrlSyms.GS___asan_memcpy.
#[local] Abbreviation GS___asan_memset := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.CtrlSyms.GS___asan_memset.

(* the two image names reduce to A's raw entries (CtrlAddr.ctrl_sigma) *)
Lemma sigma_asan_memcpy : SIGMA GS___asan_memcpy = 0x52028.
Proof. reflexivity. Qed.
Lemma sigma_asan_memset : SIGMA GS___asan_memset = 0x524c4.
Proof. reflexivity. Qed.

Lemma asan_memcpy_aintrin :
  forall B : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.asyms,
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AF0m.CtrlTSyms B ->
  aintrin_realizes SEGS B OCpy (SIGMA GS___asan_memcpy).
Proof.
intros B TB. rewrite sigma_asan_memcpy. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.aintrin_realizes.
exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AE2q.asan_memcpy_realizes B
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0q.AR_laws_ok SEGS B) TB).
Qed.

Lemma asan_memset_aintrin :
  forall B : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.asyms,
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AF0m.CtrlTSyms B ->
  aintrin_realizes SEGS B OSet (SIGMA GS___asan_memset).
Proof.
intros B TB. rewrite sigma_asan_memset. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.aintrin_realizes.
intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull _.
exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AE2r.asan_memset_realizes B
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0q.AR_laws_ok SEGS B) TB
  ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Hra Hhull Ham).
Qed.

Theorem ctrlA_asan_memcpy_realizes :
  aintrin_realizes SEGS OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AD2l.CtrlB OCpy (SIGMA GS___asan_memcpy).
Proof.
exact (asan_memcpy_aintrin OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AD2l.CtrlB
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AD2l.CtrlB_syms).
Qed.

Theorem ctrlA_asan_memset_realizes :
  aintrin_realizes SEGS OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AD2l.CtrlB OSet (SIGMA GS___asan_memset).
Proof.
exact (asan_memset_aintrin OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AD2l.CtrlB
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AD2l.CtrlB_syms).
Qed.

End IntrinA.
