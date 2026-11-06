(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8j.v:156-159
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACes.v:275-277 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACim.v:270-271 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:1527-1530, 1556-1561 [Apache-2.0 OR MIT], for libreac/fuzz_identity's
   asan-ubsan build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_D4.v, with its module paths and module names changed; 23 of its 61 lines of code are new or changed and 1040 lines of the source are left out. *)
(* The second hand statement of segment H of LLVMFuzzerTestOneInput's ASan+UBSan walk (image B): the
   put_dec call. Closed: every premise is explicit, the callee contract and the allocator laws are premises
   of the statement itself, `B` is the only parameter.

   Segment H calls put_dec twice, at 0x81960 and at 0x819ac, both with a0 = ef = SF + 496 (the 16-byte frame
   variable of the entry's class-4 side-stack frame SF), a1 = mf + 208 (the uninstrumented counter slot of
   the machine frame), a2 = the value to print and a3 = the minimum width. The work of the statement is the
   premise list of put_dec.tput_dec_spec (lib/B/Prog/put_dec.v:66-87): twr_ok and tsrc_ok of the counter slot
   (the caller's own stack window: awr_byte's first case, YCbq.awr_byte_present, and the machine stack's zero
   shadow through YG0n's al_zshadow for range_addressable / shadow_hull_vis) and of the written bytes
   [ef + n, ef + n + dec_len dv mn) (the caller's own frame: awr_byte's in_frames case with own = [(4, pos)],
   IdentBFrame.shadow_hull_vis_of_frame, YG0v.zero_shadow_range and range_addressable_sub, YC1h's
   amem_range_sub_app), plus the three disjointness side conditions and the event bound. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import put_dec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import put_dec_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
Variable B : asyms.

(* 0x81960 and 0x819ac: put_dec (ef, mf + 208, dv, mn), ef = SF + 496 in the entry's own frame. *)
Definition h_pd_call_stmt : Prop :=
  AR_laws SEGS B ->
  put_dec.tput_dec_spec B ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) pos mf SF n dv mn,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  frames Sc = [(4, pos)] -> own = [(4, pos)] -> frame_addr lyc 4 pos = SF ->
  st_nev S + k <= EV_MAX ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 2 = w64 mf -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 (SF + 496) -> getr regs 11 = w64 (mf + 208) ->
  bv_unsigned (getr regs 12) = dv -> getr regs 13 = w64 mn ->
  0 <= dv < 1000 -> 0 <= mn <= 3 ->
  mf mod 32 = 0 -> sp0 - 336 <= mf -> mf <= sp0 - 320 -> sp0 - STK <= mf - 2 * ESTACK ->
  alloc_ceiling <= ly_stk_lo lyc -> ly_stk_hi lyc <= 2 ^ 47 ->
  ly_stk_lo lyc + STK <= sp0 -> sp0 <= ly_stk_hi lyc ->
  0 <= n -> n + dec_len dv mn <= 16 ->
  val_mem SEGS (mrestrict (w_H W) memc) (mf + 208) 8 n ->
  zero_shadow (aview SEGS (w_H W) memc) SHADOW_OFF (SF + 496) 16 ->
  (forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) memc a) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_put_dec) regs memc mdc)
    (put_dec.tput_dec_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
       (SF + 496) (mf + 208) n dv mn).

End c.
End b.
End a.
