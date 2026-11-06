(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:140-147, 156-161
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACh0.v:234-238 [Apache-2.0];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC59.v:27-30 [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACai.v:155-159. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/SbDecSegA.v; 30 of its 80 lines of code are new or changed and 748 lines of the source are left out. *)
(* sb_dec (fuzz_identity.asan-ubsan 0x835d0, listing offset AF_sb_dec = 0x2e5c): the walk, chained from the
   three segment lemmas.
     SbDecSegA.v  sbd_segA  0x835d0 .. 0x836f4 (BASE + 0x2e5c .. BASE + 0x2f80): the prologue, the 32-byte
                            realignment of sp, the class-0 side-stack frame (__asan_stack_malloc_0 at 0x83640),
                            the frame header and its eight shadow bytes; it ends in sbd_at1.
     segment B, 0x836f4 .. 0x83790 (BASE + 0x2f80 .. BASE + 0x301c): the divide-by-10 digit loop, the
                            min-digits pad and the emit loop, whose body calls sb_ch (0x83774) under
                            tsb_ch_spec; sbd_at1 -> sbd_at2. Split on v: SbDecSegB.v sbd_segB_lt10 (v < 10,
                            with the emit loop as one lemma sbd_emit_loop), SbDecSegBv10a.v sbd_segB_v10a
                            (10 <= v < 100), SbDecSegBv10b.v sbd_segB_v10b (100 <= v); sbd_segB below joins them.
     SbDecSegC.v  sbd_segC  0x83790 .. 0x83830: the fake-frame release (the flag store at 0x837d0 through
                            aj_flag_store_pi) and the epilogue; sbd_at2 -> tsb_dec_post.
   The contract itself (tsb_dec_spec, tsb_dec_post, SB_DEC_STK, EV_SB_DEC) is lib/B/Prog/sb_dec.v. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaRun PaShadow PaJournal IdentBase.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import sb_ch sb_dec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
SbDecSegA SbDecSegB SbDecSegBv10a SbDecSegBv10b SbDecSegC.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require sb_dec_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section h.
Variable B : asyms.
Section walk.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM0 : astack_malloc_realizes SEGS B 0.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TLF : PALibF B.
(* the callee of the emit loop (lib/B/Prog/sb_ch.v, proved there under PALib and AR_laws) and where the
   listing's program functions start (lib/B/Prog/IdentBProgSig.v) *)
Hypothesis HSC : tsb_ch_spec B.
Hypothesis PSIG : identb_prog_sig_ok.
(* Segment B, 0x836f4 .. 0x83790, by the value: v < 10 (one digit, padded to md) is sbd_segB_lt10
   (SbDecSegB.v); 10 <= v < 100 (two digits, two sb_ch calls) is sbd_segB_v10a (SbDecSegBv10a.v);
   100 <= v (three digits, three calls) is sbd_segB_v10b (SbDecSegBv10b.v). *)
Lemma sbd_segB : sbd_segB_spec B.
Proof.
assert (L1 : sbd_segB_lt10_spec B) by (apply sbd_segB_lt10; assumption).
assert (L2 : sbd_segB_v10a_spec B) by (apply sbd_segB_v10a; assumption).
assert (L3 : sbd_segB_v10b_spec B) by (apply sbd_segB_v10b; assumption).
unfold sbd_segB_spec. intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov
  fpos S2 s1v regs1 mem1 md1 Q Hat1 Hk.
destruct (Z_lt_ge_dec v 10) as [Hv | Hv]; [|destruct (Z_lt_ge_dec v 100) as [Hv2 | Hv2]].
- exact (L1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov
           fpos S2 s1v regs1 mem1 md1 Q Hv Hat1 Hk).
- exact (L2 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov
           fpos S2 s1v regs1 mem1 md1 Q ltac:(clear - Hv Hv2; lia) Hat1 Hk).
- exact (L3 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov
           fpos S2 s1v regs1 mem1 md1 Q ltac:(clear - Hv2; lia) Hat1 Hk).
Qed.
Theorem pb_sb_dec : tsb_dec_spec B.
Proof.
unfold tsb_dec_spec.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs b v md p cap n ov
  HJc Hra0 Hra4 Hgp Htp Hal16 Hwlo Hwhi G10 G11 G12 Hv Hmd Hb8 Hb0 Hb63 Hbwin Hrec Vp Vcap Vn Vov
  Rp Rcap Rn0 Rn4 Rov HWRb HROOM Hfr8 Hev Hlive.
(* 0x835d0 .. 0x836f4: the prologue, the realignment of sp and the class-0 frame *)
eapply (sbd_segA B TL LAWS ML ASM0 SMP FFL TLF); try eassumption.
intros fpos S2 s1v regs1 mem1 md1 Hat1.
(* 0x836f4 .. 0x83790: the digit loop, the pad and the emit loop (the sb_ch calls) *)
refine (sbd_segB STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov
          fpos S2 s1v regs1 mem1 md1 _ Hat1 _).
intros regs2 mem2 md2 Hat2.
(* 0x83790 .. 0x83830: the frame release, the epilogue, and tsb_dec_post *)
exact (sbd_segC B LAWS ML ASF FFL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov
         fpos S2 regs2 mem2 md2 Hat2).
Qed.
End walk.
End h.
End f.
End d.
