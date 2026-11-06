(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made for reac-pw/fuzz_pin's ASan harness walk (LLVMFuzzerTestOneInput 0x806b4,
   fuzz_pin.asan sha256 3e4859aed23f78a6eb028120d664abda29bcb8a3bfdea5d6ee5b32b646de9d16) from
   proofs/libreac/fuzz_knock/lib/A/APgMain0.v at origin/ossv/recipes 6ebe35ba632, with its module paths changed.
   rule 24: no function proved here alone; this is segment S0 of LLVMFuzzerTestOneInput's walk, whose top claim is
   lib/A/PPgMain.v.

   SEGMENT S0 ENTRY, pc 0x806b4 .. 0x807cc, ending at ss_H (0x807d0, lib/A/PPgMainSt.v). Every address was read from
   the pinned image bytes with capstone 5.0.7. The walk, with knock's line it follows:
   - 0x806b4-0x806f4: the 128-byte save frame (13 saves at [sp0-104, sp0)), s0 = sp0, `andi sp,sp,-0x20`; the first
     run stops at 0x806f8 (knock 0x7ef14); sp1 := 32 * ((sp0 - 128) / 32) into env slot 70 (knock -192).
   - the stack region is trimmed to the saves [sp0-104, sp0) (as knock), and region 70 = [s1+16, s1+24) is added
     for the one spill `sd s8,0x10(s1)` at 0x80758 (knock [16,88)).
   - 0x806f8-0x80724: the two GOT loads (0x99050 shadow base, 0x990a8 use-after-return option), s6 := SB, the
     option test `beqz a2` at 0x8071c decided by the option cell's SLit 1, a0 := 0x60, `jal 3ca58` at 0x80724
     (__asan_stack_malloc_1, class 1); the run stops at 0x3ca58 by SR_fetch.
   - the side-stack call through aj_stack_malloc_atS (lib/A/PPgMainCall.v) with class 1 and ASM1; its premise
     count_cid 1 (frames S) < fs_frames 1 is the call-site lemma pin_fs1_site.
   - the class-1 frame facts (F = frame_addr ly 1 fpos, 128 bytes, 16 shadow bytes, the flag address at F + 120),
     the atoms 75 / 87 / 88 and the alias SB + (F >> 3) = slot 88, as knock.
   - 0x80728-0x807c8: `bnez s2` decided by HPTR 5 on F (the real-stack path 0x8073c-0x80754 is never reached),
     `sd s8,0x10(s1)`, the frame header F[0..24) = 0x41B58AB3 / 0x1ffeb / 0x806b4, the 12 shadow bytes
     f1 x4, f8, f2 x3, f8, f3 x3 (0x80794-0x807c8).
   - 0x807cc `bnez a0` with a0 = n >> 26: split with SRr_sym_branch; the taken side (-> 0x80940) is refuted by
     n < 2 ^ 26 (atom 11); the fall-through runs to 0x807d0.
   - the join into ss_H (window 400) and the hand-off to the rest of the walk (RB).
   Section hypotheses: MTL TL LAWS ML ASM1 SMP FFL MTF and RB : rt_from B MT FP POST ss_H (INV_0 B MT 0). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_pin/lib/A/PPgMain0.v, with its module paths and numbers changed; 387 of its 446 lines of code are new or changed and 228 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/owed_counter_text_A_pre.v; 26 of its 60 lines of code are new or changed and 412 lines of the source are left out. *)
(* owed_counter_text at image A: the first loop by induction on the characters left (fuel), from the nine steps
   owed_counter_text_A_L<n>.v. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import owed_counter_text_A_base.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import owed_counter_text_A_L0 owed_counter_text_A_L1
  owed_counter_text_A_L2 owed_counter_text_A_L3 owed_counter_text_A_L4 owed_counter_text_A_L5 owed_counter_text_A_L6
  owed_counter_text_A_L7 owed_counter_text_A_L8.
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
Variable GLYPHA : Z.
Variable ROSTRS : list (Z * Z).
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis SEG7 : cdc_owed_seg7_specX tfibsegs B MT CA_RLO CA_RHI GLYPHA ROSTRS 0x8438c.

Lemma oc_L_nofuel : forall n, oc_from B MT GLYPHA ROSTRS (ss_L n) (INV_L n 0).
Proof.
intros n cx E ly3 S3 W3 ms3 md3 _ _ _ (i & s & dot & _ & _ & (Hi & _) & Hf) _. lia.
Qed.
Lemma oc_L_all :
  (forall n, (n <= 8)%nat -> oc_from B MT GLYPHA ROSTRS (ss_Z n) (INV_Z n)) ->
  oc_from B MT GLYPHA ROSTRS (ss_R 18446744073709551605) (INV_R 18446744073709551605) ->
  forall fuel n, (n <= 8)%nat -> oc_from B MT GLYPHA ROSTRS (ss_L n) (INV_L n fuel).
Proof using MTL TL LAWS ML FFL SEG7.
intros HZ HR fuel. induction fuel as [|fuel IH]; intros n Hn; [apply oc_L_nofuel|].
destruct n as [|[|[|[|[|[|[|[|[|n]]]]]]]]].
- exact (oc_step0 B MT GLYPHA ROSTRS MTL TL LAWS ML FFL SEG7 fuel IH (HZ 0%nat ltac:(lia)) HR).
- exact (oc_step1 B MT GLYPHA ROSTRS MTL TL LAWS ML FFL SEG7 fuel IH (HZ 1%nat ltac:(lia)) HR).
- exact (oc_step2 B MT GLYPHA ROSTRS MTL TL LAWS ML FFL SEG7 fuel IH (HZ 2%nat ltac:(lia)) HR).
- exact (oc_step3 B MT GLYPHA ROSTRS MTL TL LAWS ML FFL SEG7 fuel IH (HZ 3%nat ltac:(lia)) HR).
- exact (oc_step4 B MT GLYPHA ROSTRS MTL TL LAWS ML FFL SEG7 fuel IH (HZ 4%nat ltac:(lia)) HR).
- exact (oc_step5 B MT GLYPHA ROSTRS MTL TL LAWS ML FFL SEG7 fuel IH (HZ 5%nat ltac:(lia)) HR).
- exact (oc_step6 B MT GLYPHA ROSTRS MTL TL LAWS ML FFL SEG7 fuel IH (HZ 6%nat ltac:(lia)) HR).
- exact (oc_step7 B MT GLYPHA ROSTRS MTL TL LAWS ML FFL SEG7 fuel IH (HZ 7%nat ltac:(lia)) HR).
- exact (oc_step8 B MT GLYPHA ROSTRS MTL TL LAWS ML FFL SEG7 fuel IH (HZ 8%nat ltac:(lia)) HR).
- lia.
Qed.
End oc.
