(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new for libreac/fuzz_boxreg (asan-ubsan); the same corollary as omx-clap-core/fuzz_manifest
   lib/A/FMgxa_mem.v:279 memset_stack_contract_Avsn (a working branch 6831b682b74), proved through an
   image-free transfer lemma (a Theorem Labs lane's measured fix, 2026-10-29: `change (img_segs A_img_vsn) with
   (img_segs A_img)` did not finish in 30 min, because conversion unfolds both symbol tables). *)
(* proves no function (kind: segment lemma -- a view lemma). A_img_vsn (RT_IImgA.v:117) has A_img's segments and
   differs from A_img only at key 0x7f000400 (A_sym_vsn_agree).  memset_stack_contract (GXA SetCall.v) reads the
   image only through img_segs and `sym 0x21738` (the memset key; RT_IImgA.v resolves it on this image), so the
   A_img contract of RT_gxa_calls_mem.v is the A_img_vsn contract.  GXA's vsnprintf takes no memcpy contract
   (G_vsnprintf.v), so there is no memcpy twin. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GXA Require Import SetCall VfprintfCall.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B Require Import RT_IImgA RT_gxa_inst.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B Require RT_gxa_calls_mem.
Module RGM := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.RT_gxa_calls_mem.
Open Scope Z_scope.

(* image-free: two records with the same segments and the same memset symbol have the same memset contract *)
Lemma memset_contract_transfer : forall (I1 I2 : RImg) R,
  @img_segs I1 = @img_segs I2 -> @sym I1 0x21738 = @sym I2 0x21738 ->
  @memset_stack_contract I1 R -> @memset_stack_contract I2 R.
Proof.
  intros [s1 y1] [s2 y2] R Hs Hy H. cbn [img_segs sym] in Hs, Hy. subst s2.
  unfold memset_stack_contract, memset_stack_post in *. cbn [img_segs sym] in *.
  rewrite <- Hy. exact H.
Qed.

Lemma A_vsn_segs_eq : @img_segs A_img = @img_segs A_img_vsn.
Proof. unfold A_img, A_img_vsn. cbn [img_segs]. reflexivity. Qed.

Lemma A_vsn_sym_memset : @sym A_img 0x21738 = @sym A_img_vsn 0x21738.
Proof. unfold A_img, A_img_vsn. cbn [sym]. symmetry. apply A_sym_vsn_agree. discriminate. Qed.

Theorem memset_stack_contract_Avsn : @memset_stack_contract A_img_vsn RGM.set_ready.
Proof.
  exact (memset_contract_transfer A_img A_img_vsn RGM.set_ready A_vsn_segs_eq A_vsn_sym_memset
           RGM.memset_stack_contract_A).
Qed.

(* musl vsnprintf at A_img_vsn with its memset contract closed: only VF (a Theorem Labs lane's guarded vfprintf piece) stays *)
Definition box_vsnprintf_x_proof (vf_ready : vf_guard) (VF : @vfprintf_guarded_stmt A_img_vsn vf_ready) :=
  fm_vsnprintf_x_proof RGM.set_ready vf_ready memset_stack_contract_Avsn VF.
