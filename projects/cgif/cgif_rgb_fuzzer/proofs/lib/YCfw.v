(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK05 YG00 YG0a YG01 YG05 YG0h YG0u YG0y YG0z YG0w YG0d YCcz.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YB1u YF9j YF9i YCeb YCe8 YCe9 YCea YE35 YE34 YE3d YE36
YCfu YCe5 YCdq YChp YCf1 YCgn YCdz YCd5.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section b.
Variable B : asyms.
Hypothesis HB : TrbSyms B.
Hypothesis TL : TrbLib B.
Hypothesis AMALLOC : amalloc_realizes trbsegs B.
Hypothesis AFREE : afree_realizes trbsegs B.
Hypothesis ASM1 : astack_malloc_realizes trbsegs B 1.
Hypothesis ASM2 : astack_malloc_realizes trbsegs B 2.
Let LAWS : AR_laws trbsegs B := AR_laws_ok trbsegs B.
Let ML : model_laws (as_universe B) := model_laws_ok (as_universe B) (ts_universe B HB).
Lemma link_SMP : stack_malloc_progressP B.
Proof. intros s cid W Hc Hn. exact (stack_malloc_progress (as_universe B) s cid W Hc Hn). Qed.
Lemma link_FFL : frame_flag_lawP trbsegs B.
Proof.
intros ly S W mem md cid pos HAR Hin.
destruct (al_flag _ _ LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
destruct (al_client_img _ _ LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof HAR as (M & L & _). pose proof (trb_img_cover ly S md L) as [C1 C2]. unfold TRB_IMG_LO, TRB_IMG_END in C1, C2.
destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
split; [exact Hp|]. split; [exact Ho|]. split.
- split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
- split; [exact H4096|]. split; [|exact Hceil]. unfold zone2, off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma link_ASF : astack_free_law trbsegs B.
Proof. exact (astack_free_law_ok trbsegs B). Qed.
Lemma link_AMEMSET : aintrin_realizes trbsegs B OSet YCfu.A_asan_memset.
Proof.
intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull _.
exact (asan_memset_realizes B LAWS HB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Hra Hhull Ham).
Qed.
Lemma link_AMEMCPY : aintrin_realizes trbsegs B OCpy YCfu.A_asan_memcpy.
Proof.
intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull Hsrc.
exact (asan_memcpy_realizes B LAWS HB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull Hsrc).
Qed.
Lemma link_AMEMCMP : amemcmp_realizes trbsegs B YCe5.A_memcmp_icpt.
Proof. exact (memcmp_icpt_contract B LAWS HB). Qed.
Lemma link_ABCMP : abcmp_realizes trbsegs B YCdq.A_bcmp_icpt.
Proof. exact (bcmp_icpt_contract B LAWS HB). Qed.
Definition trb_liblink_contract : Prop :=
trawnew_spec B /\ tflush_spec B /\ tnewgif_spec B /\ taddframe_specG B /\ tclose_spec B.
Theorem trb_LIBLINK : trb_liblink_contract.
Proof.
pose proof link_SMP as SMP. pose proof link_FFL as FFL. pose proof link_ASF as ASF.
pose proof link_AMEMSET as AMEMSET. pose proof link_AMEMCPY as AMEMCPY.
pose proof link_AMEMCMP as AMEMCMP. pose proof link_ABCMP as ABCMP.
assert (RAWNEW : trawnew_spec B) by (eapply (trb_cgif_raw_newgif B); eassumption).
assert (FLUSH : tflush_spec B) by (eapply (trb_flushFrame B); eassumption).
assert (TNEWGIF : tnewgif_spec B) by (eapply (trb_cgif_newgif B); eassumption).
assert (TADDF : taddframe_specG B) by (eapply (trb_cgif_addframeG B); eassumption).
assert (TCLOSE : tclose_spec B) by (eapply (trb_cgif_close B); eassumption).
exact (conj RAWNEW (conj FLUSH (conj TNEWGIF (conj TADDF TCLOSE)))). (* [comment removed for export] *)
Qed.
End b.
End a.
