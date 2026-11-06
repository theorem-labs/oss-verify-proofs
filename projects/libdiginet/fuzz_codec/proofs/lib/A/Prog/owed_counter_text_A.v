(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgRt.v (rt_hand, fs_roF / fs_rwF) and
   APgStep.v (same_io_wvb) at 6ebe35ba632; adapted to the class-0 frame and the exit of reac_box_pin_parse. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_pin/lib/A/PPgParse4.v, with its module paths and module names changed; 262 of its 291 lines of code are new or changed and 251 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/check_personality_A.v, with its module names changed; 104 of its 132 lines of code are new or changed and 263 lines of the source are left out. *)
(* owed_counter_text (fuzz_codec.c:402-429) at image A (fuzz_codec.asan, entry 0x83df8): the walk assembled.
   owed_counter_text_A_pre.v: the entry to the first loop's head (frame request, shadow map, memset);
   owed_counter_text_A_L<n>.v / _Lind.v: the first loop by induction on the characters left;
   owed_counter_text_A_Z<n>.v and _Q<n><b>*.v: the second loop (seg[8] and *dots);
   owed_counter_text_A_R.v: the release (shadow marks, the frame's header, the flag cleared) and the return. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85 YCeo.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgChkC CPgWalk CPgWalkKept CPgWalkFrame CPgWalkCall.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import owed_counter_text_A_base owed_counter_text_A_Lt owed_counter_text_A_wr owed_counter_text_A_Qb owed_counter_text_A_Rb.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import owed_counter_text_A_pre owed_counter_text_A_Lind owed_counter_text_A_R0 owed_counter_text_A_RE.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import
  owed_counter_text_A_Q1f
  owed_counter_text_A_Q1t
  owed_counter_text_A_Q2f
  owed_counter_text_A_Q2t
  owed_counter_text_A_Q3f
  owed_counter_text_A_Q3t
  owed_counter_text_A_Q4f
  owed_counter_text_A_Q4t
  owed_counter_text_A_Q5fa
  owed_counter_text_A_Q5fb
  owed_counter_text_A_Q5ta
  owed_counter_text_A_Q5tb
  owed_counter_text_A_Q6fa
  owed_counter_text_A_Q6fb
  owed_counter_text_A_Q6ta
  owed_counter_text_A_Q6tb
  owed_counter_text_A_Q7fa
  owed_counter_text_A_Q7fb
  owed_counter_text_A_Q7ta
  owed_counter_text_A_Q7tb
  owed_counter_text_A_Q8fa
  owed_counter_text_A_Q8fb
  owed_counter_text_A_Q8ta
  owed_counter_text_A_Q8tb
  owed_counter_text_A_Z0
  owed_counter_text_A_Z1
  owed_counter_text_A_Z2
  owed_counter_text_A_Z3
  owed_counter_text_A_Z4
  owed_counter_text_A_Z5
  owed_counter_text_A_Z6
  owed_counter_text_A_Z7
  owed_counter_text_A_Z8.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require AE36.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.


Section oc. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis ASM1 : astack_malloc_realizes tfibsegs B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis AMEMSET : aintrin_realizes tfibsegs B OSet 0x51e34.
Section g.
Variable GLYPHA : Z.
Variable ROSTRS : list (Z * Z).
Hypothesis SEG7 : cdc_owed_seg7_specX tfibsegs B MT CA_RLO CA_RHI GLYPHA ROSTRS 0x8438c.
Lemma oc_Z_all : oc_from B MT GLYPHA ROSTRS (ss_R 0) (INV_R 0) ->
  oc_from B MT GLYPHA ROSTRS (ss_R 18446744073709551605) (INV_R 18446744073709551605) ->
  forall n, (n <= 8)%nat -> oc_from B MT GLYPHA ROSTRS (ss_Z n) (INV_Z n).
Proof using MTL TL LAWS ML FFL.
intros HR0 HRE n Hn.
destruct n as [|[|[|[|[|[|[|[|[|n]]]]]]]]].
- exact (oc_z0 B MT GLYPHA ROSTRS MTL TL LAWS ML FFL HR0).
- apply (oc_z1 B MT GLYPHA ROSTRS MTL TL LAWS ML FFL). intros [|].
  + exact (oc_q1_7t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL HR0 HRE).
  + exact (oc_q1_7f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL HR0 HRE).
- apply (oc_z2 B MT GLYPHA ROSTRS MTL TL LAWS ML FFL). intros [|].
  + exact (oc_q2_6t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q2_7t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL HR0 HRE)).
  + exact (oc_q2_6f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q2_7f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL HR0 HRE)).
- apply (oc_z3 B MT GLYPHA ROSTRS MTL TL LAWS ML FFL). intros [|].
  + exact (oc_q3_5t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q3_6t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q3_7t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL HR0 HRE))).
  + exact (oc_q3_5f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q3_6f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q3_7f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL HR0 HRE))).
- apply (oc_z4 B MT GLYPHA ROSTRS MTL TL LAWS ML FFL). intros [|].
  + exact (oc_q4_4t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q4_5t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q4_6t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q4_7t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL HR0 HRE)))).
  + exact (oc_q4_4f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q4_5f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q4_6f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q4_7f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL HR0 HRE)))).
- apply (oc_z5 B MT GLYPHA ROSTRS MTL TL LAWS ML FFL). intros [|].
  + exact (oc_q5_3t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q5_4t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q5_5t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q5_6t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q5_7t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL HR0 HRE))))).
  + exact (oc_q5_3f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q5_4f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q5_5f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q5_6f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q5_7f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL HR0 HRE))))).
- apply (oc_z6 B MT GLYPHA ROSTRS MTL TL LAWS ML FFL). intros [|].
  + exact (oc_q6_2t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q6_3t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q6_4t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q6_5t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q6_6t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q6_7t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL HR0 HRE)))))).
  + exact (oc_q6_2f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q6_3f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q6_4f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q6_5f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q6_6f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q6_7f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL HR0 HRE)))))).
- apply (oc_z7 B MT GLYPHA ROSTRS MTL TL LAWS ML FFL). intros [|].
  + exact (oc_q7_1t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q7_2t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q7_3t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q7_4t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q7_5t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q7_6t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q7_7t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL HR0 HRE))))))).
  + exact (oc_q7_1f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q7_2f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q7_3f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q7_4f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q7_5f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q7_6f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q7_7f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL HR0 HRE))))))).
- apply (oc_z8 B MT GLYPHA ROSTRS MTL TL LAWS ML FFL). intros [|].
  + exact (oc_q8_0t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q8_1t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q8_2t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q8_3t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q8_4t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q8_5t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q8_6t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q8_7t B MT GLYPHA ROSTRS MTL TL LAWS ML FFL HR0 HRE)))))))).
  + exact (oc_q8_0f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q8_1f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q8_2f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q8_3f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q8_4f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q8_5f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q8_6f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL (oc_q8_7f B MT GLYPHA ROSTRS MTL TL LAWS ML FFL HR0 HRE)))))))).
- lia.
Qed.
Lemma oc_walk : forall cx0, oc_pre B GLYPHA ROSTRS cx0 ->
  SRr tfibsegs (o_W cx0) (cfg_at tfibsegs 0x83df8 (o_regs cx0) (o_memc cx0) (o_mdc cx0)) (oc_post B MT cx0).
Proof using MTL TL LAWS ML MTF ASM1 SMP FFL ASF AMEMSET SEG7.
intros cx0 Hpre.
pose proof (oc_rel0 B MT GLYPHA ROSTRS MTL TL LAWS ML FFL MTF ASF) as HR0.
pose proof (oc_relE B MT GLYPHA ROSTRS MTL TL LAWS ML FFL MTF ASF) as HRE.
apply (oc_prefix B MT GLYPHA ROSTRS MTL TL LAWS ML ASM1 SMP MTF FFL AMEMSET cx0 Hpre).
intros fuel.
exact (oc_L_all B MT GLYPHA ROSTRS MTL TL LAWS ML FFL SEG7 (oc_Z_all HR0 HRE) HRE fuel 0 ltac:(lia)).
Qed.
End g.
Hypothesis OWED : cdc_owed_seg7_specX tfibsegs B MT CA_RLO CA_RHI CA_GLYPH CA_ROSTRS 0x8438c.
Theorem owed_counter_text_A_holds :
  cdc_owed_counter_text_specX tfibsegs B MT CA_RLO CA_RHI CA_GLYPH CA_ROSTRS 0x83df8.
Proof using MTL TL LAWS ML MTF ASM1 SMP FFL ASF AMEMSET OWED.
unfold cdc_owed_counter_text_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q sg dt tb sj dj
  HE H10 Hcstr Hcq Hcsg H11 Hdsg Hgsj Hlsj H12 Hdt Hdj Hdsd Hdqs Hdqd Hcimg Hfr8.
exact (oc_walk CA_GLYPH CA_ROSTRS OWED (mkOC STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q sg dt tb sj dj 0)
  (conj HE (conj H10 (conj Hcstr (conj Hcq (conj Hcsg (conj H11 (conj Hdsg (conj Hgsj (conj Hlsj (conj H12 (conj Hdt
   (conj Hdj (conj Hdsd (conj Hdqs (conj Hdqd (conj Hcimg Hfr8))))))))))))))))).
Qed.
End oc.
