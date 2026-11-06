(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* LLVMFuzzerTestOneInput_segX_crt1_calls: the call-site discharge of the one RUNTIME call of image B's
   LLVMFuzzerTestOneInput segment crt1 that is not a program leaf: __asan_memset of the decode buffer at +0x6d4.
   lib/Reusable/YCbq.v:1955 aj_intrin_at does the work; what is left is to read its premises off the caller's
   journal and the allocator laws: the buffer is a block this function allocated (so every byte of it is a
   writable byte of the journal's temporary set, and none of it is in the callee's stack window), it lies in
   application memory (YCbq.v:2012 amem_range_of_block), its shadow is addressable (:2687
   range_addressable_of_block) and visible (:1945 shadow_hull_vis_of_block). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n YP09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YG0v YCbq YI00 YI04 YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YI16.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import DecodeCallocKit.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBAddr.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import check_round_trip_cg.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import LLVMFuzzerTestOneInput_cg.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import LLVMFuzzerTestOneInput_segX_crt1_crt.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import LLVMFuzzerTestOneInput_segX_crt1_fevt.
Import ListNotations.
Open Scope Z_scope.

Section C1Calls.
Context {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws decodesegsB0 B.
Local Notation segs := decodesegsB0.
Local Notation sink := dec_B_sink_head.

(* The call of __asan_memset(buffer, 0xa5, olen) at +0x6d4: the journal is kept, the buffer is filled with the
   fill byte, and every other byte outside the callee's stack window is kept. *)
Lemma c1e_memset_call :
  (forall fx : YK11.FPState, @aintrin_realizes fx rc segs B OSet (decodeb_sigma DB___asan_memset)) ->
  forall (fx : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdc k
         (regsT : bvmap 5 word) (o out n : Z) (raw : word),
  @ajournal rc sink segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdc k ->
  In (out, n) (ablocks B lyc Sc) -> ~ In (out, n) (ablocks B ly S) ->
  0 < req_size n < 2 ^ 32 ->
  YK11.getr regsT 10 = w64 out -> YK11.getr regsT 11 = w64 165 ->
  YK11.getr regsT 12 = w64 (req_size n) ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  YK11.getr regsT 3 = w64 (as_gp B) -> YK11.getr regsT 4 = w64 (as_tp B) ->
  YK11.getr regsT 1 = raw -> YK0s.ret_ok raw ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (decodeb_sigma DB___asan_memset)) memT (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       @ajournal rc sink segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
       aregs_preserved regsT regs2 /\
       YK11.getr regs2 10 = w64 out /\
       (forall i, 0 <= i < req_size n -> aview segs (w_H W) mem2 (out + i) = Some (165 mod 256)) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (out <= a < out + req_size n) ->
          ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
  intros AMS fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdc k regsT o out n raw
    HJ Hin Hnin Hn R10 R11 R12 Hsp Hal Hneg Hbud Rgp Rtp Rra Hraw.
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
  destruct Hstatic as (Hal16 & Hstk0 & Hceil & Hlo & Hhi & H47 & Hbot & Htop).
  pose proof (@alloc_ceiling_val rc) as (Hac & _).
  pose proof (al_blocks _ _ LAWS lyc Sc W memT mdc out n HAR Hin)
    as (Hm16 & Hp4096 & Hpc & Happ & Hbpres & _).
  assert (HES : ESTACK = 4096) by reflexivity.
  eapply (aj_intrin_at segs B LAWS c1f_segs_low OSet (decodeb_sigma DB___asan_memset) (AMS fx)
            W regsT memT STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdc k out 165 (req_size n) o raw HJ
            R10 R11 R12 ltac:(lia) ltac:(lia) ltac:(lia) Hsp Hal Hneg Hbud Rgp Rtp Rra Hraw).
  - intros a Ha. split.
    + right. right. left. exists out, n. split; [exact Hin | split; [exact Hnin | exact Ha]].
    + lia.
  - eapply (amem_range_of_block segs B LAWS lyc Sc W memT mdc out n out (req_size n) HAR Hin); lia.
  - eapply (range_addressable_of_block segs B LAWS lyc Sc W memT mdc out n out (req_size n) HAR Hin); lia.
  - intros _. eapply (shadow_hull_vis_of_block segs B LAWS lyc Sc W memT mdc out n out (req_size n) HAR Hin);
      lia.
  - exact I.
Qed.

(* The call of check_round_trip at +0x68c (and the exit segment's at +0xaa0): everything the contract
   (lib/B/Prog/check_round_trip_cg.v dec_check_round_trip_cg) asks for, at a call made from this function's frame
   (STK = DEC_LLVMF_STK, s0 = the entry sp, the call's sp at most 240 bytes below it), with the two call-context
   premises built from the slot pre's own chain and the frame record the prologue wrote below the entry sp
   (LLVMFuzzerTestOneInput_segX_crt1_crt.v c1c_chain / c1c_ctx), and the calloc depth premise read off the
   caller's astk_ok (YCbq.v:333-335; ly_bot follows ly_top, which layout_le keeps). *)
Lemma c1e_crt_call :
  forall (MT : ameter_ops) (RA_LLVMF : Z),
  (forall fx : YK11.FPState,
     @dec_check_round_trip_cg fx rc B MT (decodeb_sigma DB_check_round_trip) (CTX_check_round_trip RA_LLVMF)) ->
  forall (fx : YK11.FPState) sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
         (regs : bvmap 5 word) (s0c audio pcm nch ns bA nA bP nP T : Z),
  @ajournal rc sink segs B DEC_LLVMF_STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  @achain rc ly (aview segs (w_H W0) mem0) sp0 s0c [] ->
  rdword (aview segs (w_H W) memc) (sp0 - 8) = Some RA_LLVMF ->
  rdword (aview segs (w_H W) memc) (sp0 - 16) = Some s0c ->
  4096 <= RA_LLVMF ->
  (raZ regs = DEC_A_LLVMF + 0x690 \/ raZ regs = DEC_A_LLVMF + 0xaa4) ->
  YK0s.ret_ok (YK11.getr regs 1) ->
  YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
  YK11.getr regs 10 = w64 audio -> YK11.getr regs 11 = w64 pcm ->
  YK11.getr regs 12 = w64 nch -> YK11.getr regs 13 = w64 ns ->
  s0Z regs = sp0 ->
  spZ regs mod 16 = 0 -> sp0 - 240 <= spZ regs -> spZ regs + 16 <= sp0 ->
  frm_zero (@fp_csr fx) ->
  Z.even nch = true -> 2 <= nch <= 127 -> 1 <= ns <= 12 -> 3 * nch * ns <= 1440 ->
  In (bA, nA) (ablocks B lyc Sc) -> bA <= audio -> audio + 3 * nch * ns <= bA + nA ->
  In (bP, nP) (ablocks B lyc Sc) -> bP <= pcm -> pcm + 3 * nch * ns <= bP + nP ->
  dec_crt_braid (aview segs (w_H W) memc) audio pcm nch ns ->
  dec_rom_view_rd W memc ->
  st_nev S + k + DEC_CRT_EV <= EV_MAX -> blocks_bytes Sc + DEC_CRT_LIVE <= LIVE_MAX ->
  mo_ok MT Sc T -> dec_crt_cost MT nch ns <= T ->
  SRr segs W (@cfg_at fx segs (decodeb_sigma DB_check_round_trip) regs memc mdc)
    (@dec_crt_post rc B MT DEC_LLVMF_STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs nch ns).
Proof.
  intros MT RA_LLVMF ICRT fx sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
    s0c audio pcm nch ns bA nA bP nP T
    HJ HCH0 HS8 HS16 HRA4 Hra Hret Rgp Rtp R10 R11 R12 R13 Hs0 Hal16' Hsp240 Hsp16
    Hfrm Hev2 Hnch Hns Hreg HinA HbA1 HbA2 HinP HbP1 HbP2 HBR HROM Hnev Hlive Hmo Hcost.
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & Hpres & Hstatic & _).
  destruct Hstatic as (Hal16 & Hstk0 & Hceil & Hlo & Hhi & H47 & Hbot & Htop1 & Htop2).
  destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
  pose proof (@YM05.alloc_ceiling_val rc) as (Hac & _).
  assert (HSTK : DEC_LLVMF_STK = 32768) by reflexivity.
  assert (HKEEP : forall a, sp0 <= a < 2 ^ 64 -> aview segs (w_H W) memc a = aview segs (w_H W0) mem0 a).
  { intros a Ha. apply F1; lia. }
  destruct (c1c_chain ly lyc (aview segs (w_H W0) mem0) (aview segs (w_H W) memc) sp0 s0c (spZ regs) RA_LLVMF
              HCH0 Etop ltac:(lia) HKEEP HS8 HS16 HRA4 ltac:(lia) ltac:(lia) ltac:(lia)) as (ch & HCH & HSP).
  assert (HRAZ : 4096 <= raZ regs).
  { assert (EA : 4096 <= DEC_A_LLVMF) by (vm_compute; discriminate). destruct Hra as [-> | ->]; lia. }
  eapply (ICRT fx DEC_LLVMF_STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
            audio pcm nch ns bA nA bP nP T ch); try eassumption.
  - rewrite Hs0. exact HCH.
  - apply c1c_ctx; [exact Hra | exact HSP].
  - unfold DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *. lia.
  - lia.
  - unfold ly_bot in *. rewrite Etop.
    unfold DEC_CALLOC_DEPTH, DEC_CRT_FRAME, ASTACK in *. lia.
Qed.
End C1Calls.
