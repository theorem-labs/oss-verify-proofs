(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACez.v, with its module paths and module names changed; 22 of its 48 lines of code are new or changed and 214 lines of the source are left out. *)
(* diginet_counter_text (diginet_codec.c:337-369) at its address in image B (fuzz_codec.asan-ubsan, 0x869e4) against
   its B-level contract cdcU_counter_text_specX (lib/AU/Prog/CPgChkU.v): the four segment lemmas
   (diginet_counter_text_B_s0.v, _l1.v, _l2.v, _x.v) composed by the boundary layer (diginet_counter_text_B_inv.v,
   ct_spec_of_segs: the two loops closed by induction), with ct_now derived from the contract's premises
   (diginet_counter_text_B_now.v).
   Premises: the contract of diginet_seg7 at 0x86978, the class-1 side-stack frame request (astack_malloc_realizes),
   its release (astack_free_law) and __asan_memset at 0x51f84 (aintrin_realizes OSet), as the contract's callees;
   besides them, one fact of the image the seg7 call needs at its call state: the read window [RLO, RHI) lies in
   the image (the image's read-only data keeps its bytes there through what the call kept). Section
   hypotheses: the meter and the runtime laws (ameter_laws, TfibLib, AR_laws, model_laws), the frame request's
   progress (stack_malloc_progressP), the frame's flag law (frame_flag_lawP) and the meter's frame-state laws
   (ameter_fs_laws). *)
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
diginet_counter_text_B_inv diginet_counter_text_B_now
diginet_counter_text_B_s0 diginet_counter_text_B_l1 diginet_counter_text_B_l2 diginet_counter_text_B_x.
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
Theorem diginet_counter_text_B_holds : forall RLO RHI SEG7TBL,
  cdcU_seg7_specX tfibsegs B MT RLO RHI SEG7TBL 0x86978 -> astack_malloc_realizes tfibsegs B 1 ->
  astack_free_law tfibsegs B -> aintrin_realizes tfibsegs B OSet 0x51f84 ->
  (forall a, RLO <= a < RHI -> in_img tfibsegs a) ->
  cdcU_counter_text_specX tfibsegs B MT RLO RHI SEG7TBL 0x869e4.
Proof.
intros RLO RHI SEG7TBL SEG7 ASM1 ASF AIS HRELRO.
change 0x869e4 with B_CT. change 0x86978 with B_SEG7 in SEG7.
apply (ct_spec_of_segs B MT RLO RHI SEG7TBL).
- eapply ct_s0_holds; eassumption.
- eapply ct_l1_holds; eassumption.
- eapply ct_l2_holds; eassumption.
- eapply ct_x_holds; eassumption.
- intros g Hpre Hpre2. exact (ct_now_of B LAWS RLO RHI SEG7TBL HRELRO g Hpre Hpre2).
Qed.
End d.
End b.
