(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK05 YG00 YG0a YG01 YG05 YG0h YG0u YG0y YG0z YG0w YG0d YG0e YG0f YCcz.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YB1u YF9j YF9i YCeb YCe8 YCe9 YCea YCfw
YCi1 YCie YCph YCpi YCi2 YCin YCi7 YCia YCrc
YCi4 YCi0 YCio YCi6 YCi9 YCik YCi5
YCjr YCpj YCq4 YCq5 YCq6 YCnk YCni YCod YCnn YCpd
YCp4 YCi8 YCn3 YCql.
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
Hypothesis ASM7 : forall fx : YK11.FPState, @astack_malloc_sz_realizes fx rc trbsegs B A_stack_malloc_7 7.
Hypothesis ASF7 : forall fx : YK11.FPState, @astack_free_realizes fx rc trbsegs B A_stack_free_7 7.
Hypothesis ASS00 : forall fx : YK11.FPState, @aset_shadow_realizes fx rc trbsegs B A_set_shadow_00 0.
Hypothesis ASSF8 : forall fx : YK11.FPState, @aset_shadow_realizes fx rc trbsegs B A_set_shadow_f8 248.
Hypothesis FPC : trb_fp_consts B.
Hypothesis ROLC : trb_rol_const B.
Hypothesis AREALLOC : forall fx : YK11.FPState, @arealloc_realizes fx rc trbsegs B 0x533cc 0x53904.
Let LAWS : AR_laws trbsegs B := AR_laws_ok trbsegs B.
Let ML : model_laws (as_universe B) := model_laws_ok (as_universe B) (ts_universe B HB).
Lemma rl2_SMP : stack_malloc_progressP B. Proof. eapply link_SMP; eassumption. Qed.
Lemma rl2_FFL : frame_flag_lawP trbsegs B. Proof. eapply link_FFL; eassumption. Qed.
Lemma rl2_AMEMSET : forall fx : YK11.FPState, @aintrin_realizes fx rc trbsegs B OSet YCfu.A_asan_memset.
Proof. intros fx. eapply link_AMEMSET; eassumption. Qed.
Lemma rl2_AMEMCPY : forall fx : YK11.FPState, @aintrin_realizes fx rc trbsegs B OCpy YCfu.A_asan_memcpy.
Proof. intros fx. eapply link_AMEMCPY; eassumption. Qed.
Lemma rl2_ABCMP : forall fx : YK11.FPState, @abcmp_realizes fx rc trbsegs B YCdq.A_bcmp_icpt.
Proof. intros fx. eapply link_ABCMP; eassumption. Qed.
Lemma rl2_LL : forall fx : YK11.FPState, @trb_liblink_contract fx rc B.
Proof. intros fx. eapply (@trb_LIBLINK fx rc B); [exact HB | exact TL | apply AMALLOC | apply AFREE | apply ASM1 | apply ASM2]. Qed.
Theorem trb_RGBADDV : forall fx : YK11.FPState, @trgb_addframe_specV fx rc B.
Proof.
pose proof rl2_SMP as SMP. pose proof rl2_FFL as FFL. pose proof rl2_AMEMSET as AMEMSET. pose proof rl2_AMEMCPY as AMEMCPY. pose proof rl2_ABCMP as ABCMP.
apply (@trgb_addframe_closedV rc B TL LAWS ML SMP FFL ASM7 ASSF8 ASS00 ASF7 AMALLOC AFREE AMEMSET AMEMCPY ABCMP).
- intros fx. destruct (rl2_LL fx) as (RAWNEW & FLUSH & TNEWGIF & TADDF & TCLOSE). exact TADDF.
- intros fx. eapply (@trb_free_decision_treeV fx rc B); try eassumption. apply AFREE.
- intros fx. eapply (@trb_free_col_hash_table fx rc B); try eassumption. apply AFREE.
- intros fx. eapply (@trb_col_hash fx rc B); try eassumption. apply ABCMP.
- eapply (@trb_new_tree_node2V rc B); eassumption.
- intros fx. eapply (@trb_get_palette rc B); try eassumption. intros fy. eapply (@trb_round rc B); eassumption.
- intros fx. eapply (@trb_get_leave_node_index rc B); eassumption.
- exact ROLC.
- intros fx. eapply (@trb_getPixelVal fx rc B); eassumption.
- exact AREALLOC.
Qed.
Theorem trb_RLIBCV2 : trb_rlibV_contract_all B.
Proof. exact (@trb_RLIBCV rc B HB TL AMALLOC AFREE ASM1 ASM2 trb_RGBADDV). Qed.
End a.
