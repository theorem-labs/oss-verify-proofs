(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK05 YG00 YG0a YG01 YG05 YG0h YG0u YG0y YG0z YG0w YG0d YG0e YCcz.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YB1u YF9j YF9i YCeb YCe8 YCe9 YCea YCfw YF9q
YCi1 YCie YCph YCpi YCrr YCrc
YCid YChz YCrq YCr6.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section a.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis HB : TrbSyms B.
Hypothesis TL : TrbLib B.
Hypothesis AMALLOC : forall fx : YK11.FPState, @amalloc_realizes fx rc trbsegs B.
Hypothesis AFREE : forall fx : YK11.FPState, @afree_realizes fx rc trbsegs B.
Hypothesis ASM1 : forall fx : YK11.FPState, @astack_malloc_realizes fx rc trbsegs B 1.
Hypothesis ASM2 : forall fx : YK11.FPState, @astack_malloc_realizes fx rc trbsegs B 2.
Hypothesis TRGBADDV : forall fx : YK11.FPState, @trgb_addframe_specV fx rc B.
Theorem trb_RLIBCV : trb_rlibV_contract_all B.
Proof.
assert (LAWS : AR_laws trbsegs B) by exact (AR_laws_ok trbsegs B).
assert (ML : model_laws (as_universe B)) by exact (model_laws_ok (as_universe B) (ts_universe B HB)).
assert (SMP : stack_malloc_progressP B) by (eapply link_SMP; eassumption).
assert (FFL : frame_flag_lawP trbsegs B) by (eapply link_FFL; eassumption).
assert (ASF : astack_free_law trbsegs B) by (eapply link_ASF; eassumption).
assert (AMEMSET : forall fx : YK11.FPState, @aintrin_realizes fx rc trbsegs B OSet YCfu.A_asan_memset) by (intros fx; eapply link_AMEMSET; eassumption).
assert (AMEMCPY : forall fx : YK11.FPState, @aintrin_realizes fx rc trbsegs B OCpy YCfu.A_asan_memcpy) by (intros fx; eapply link_AMEMCPY; eassumption).
assert (ASM0 : forall fx : YK11.FPState, @astack_malloc_sz_realizes fx rc trbsegs B YCrr.A_stack_malloc_0 0)
by (intros fx; exact (@trb_stack_malloc_0 fx rc B LAWS HB)).
assert (LL : forall fx : YK11.FPState, @trb_liblink_contract fx rc B)
by (intros fx; eapply (@trb_LIBLINK fx rc B); [exact HB | exact TL | apply AMALLOC | apply AFREE | apply ASM1 | apply ASM2]).
assert (TRGBNEWGIF : forall fx : YK11.FPState, @trgb_newgif_spec fx rc B).
{ intros fx. destruct (LL fx) as (RAWNEW & FLUSH & TNEWGIF & TADDF & TCLOSE).
eapply (@trb_cgif_rgb_newgif fx rc B); try eassumption; first [apply AMALLOC | apply AFREE | apply ASM1 | apply AMEMSET | apply AMEMCPY]. }
assert (TRGBCLOSE : forall fx : YK11.FPState, @trgb_close_spec fx rc B).
{ intros fx. destruct (LL fx) as (RAWNEW & FLUSH & TNEWGIF & TADDF & TCLOSE).
eapply (@trb_cgif_rgb_close fx rc B); try eassumption; apply AFREE. }
assert (TRRFC : forall fx : YK11.FPState, @trrfc_spec fx rc B).
{ intros fx. eapply (@trb_rrfc fx rc B); try eassumption; first [apply AMALLOC | apply AFREE | apply AMEMSET | apply AMEMCPY | apply ASM0]. }
pose proof TRGBADDV as TRGBADD.
eapply (@trb_rlib rc B); try eassumption; first [apply AFREE | apply AMEMSET | apply AMEMCPY | apply ASM2].
Qed.
End a.
