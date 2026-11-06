(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACez.v, with its module paths and module names changed; 22 of its 48 lines of code are new or changed and 214 lines of the source are left out. *)
(* owed_counter_text (fuzz_codec.c:405-430) at its address in image B (fuzz_codec.asan-ubsan, 0x84474) against its
   B-level contract cdcU_owed_counter_text_specX (lib/AU/Prog/CPgChkU.v): the four segment lemmas
   (owed_counter_text_B_s0.v, _l1.v, _l2.v, _x.v) composed by the boundary layer (owed_counter_text_B_inv.v,
   oc_spec_of_segs: the two loops closed by induction), with oc_now derived from the contract's premises
   (owed_counter_text_B_now.v).
   Premises: the contract of owed_seg7 at 0x84a54, the class-1 side-stack frame request (astack_malloc_realizes),
   its release (astack_free_law) and __asan_memset at 0x51f84 (aintrin_realizes OSet), as the contract's callees;
   besides them, one fact of the image the owed_seg7 call needs at its call state: the read window [RLO, RHI) lies in
   the image (the image's read-only data keeps its bytes there through what the call kept). Section hypotheses: the
   meter and the runtime laws (ameter_laws, TfibLib, AR_laws, model_laws), the frame request's progress
   (stack_malloc_progressP), the frame's flag law (frame_flag_lawP, the contracts' form) and the meter's frame-state
   laws (ameter_fs_laws). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCeh.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgEncU CPgChkU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import
owed_counter_text_B_inv owed_counter_text_B_now
owed_counter_text_B_s0 owed_counter_text_B_l1 owed_counter_text_B_l2 owed_counter_text_B_x.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis MTF : ameter_fs_laws MT.
Theorem owed_counter_text_B_holds : forall RLO RHI GLYPHA ROSTRS,
  cdcU_owed_seg7_specX tfibsegs B MT RLO RHI GLYPHA ROSTRS 0x84a54 -> astack_malloc_realizes tfibsegs B 1 ->
  astack_free_law tfibsegs B -> aintrin_realizes tfibsegs B OSet 0x51f84 ->
  (forall a, RLO <= a < RHI -> in_img tfibsegs a) ->
  cdcU_owed_counter_text_specX tfibsegs B MT RLO RHI GLYPHA ROSTRS 0x84474.
Proof.
intros RLO RHI GLYPHA ROSTRS SEG7 ASM1 ASF AIS HRELRO.
change 0x84474 with B_OCT. change 0x84a54 with B_OSEG7 in SEG7.
apply (oc_spec_of_segs B MT RLO RHI GLYPHA ROSTRS).
- eapply oc_s0_holds; eassumption.
- eapply oc_l1_holds; eassumption.
- eapply oc_l2_holds; eassumption.
- eapply oc_x_holds; eassumption.
- intros g Hpre Hpre2. exact (oc_now_of B LAWS RLO RHI GLYPHA ROSTRS HRELRO g Hpre Hpre2).
Qed.
End d.
End b.
