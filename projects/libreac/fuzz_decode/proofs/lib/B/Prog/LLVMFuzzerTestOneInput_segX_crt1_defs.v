(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* LLVMFuzzerTestOneInput_segX_crt1_defs: the cut points inside image B's LLVMFuzzerTestOneInput segment crt1
   (+0x5cc .. +0x6ec) and the three continuations the head of the segment (+0x5cc .. the first call) hands over to:
     c1_pre      what the slot pre (dec_b_base, dec_b_rom) gives the segment;
     c1_st       the state at a call: the frame invariant (dec_b_core), the blocks, the meter, the memory clauses
                 (LLVMFuzzerTestOneInput_segX_crt1_cut.v c1_mem) and the spill of copy + 50 at 80(s1);
     c1_regs     the callee-saved registers every cut point of the stretch states;
     c1_K_crt    from the call of check_round_trip at +0x68c (0 < ns <= 12, the decode succeeded),
     c1_K_braid  from the call of check_braid at +0x6bc (the decode succeeded, after check_round_trip or not),
     c1_K_memset from the call of __asan_memset at +0x6d4,
   each to the segment's end state llvm_b_st_6f0 (lib/B/Prog/LLVMFuzzerTestOneInput_segs.v).  The head before the
   check_round_trip call has used none of the meter or the events of +0x68c; the other two are entered with the
   whole segment's (dec_ev_6f0, dec_spent_6f0, dec_rest_6f0). *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YP09 YI00 YI04.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBAddr check_round_trip_cg
  LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import LLVMFuzzerTestOneInput_segX_crt1_cut.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require LeafCgKit.
Import ListNotations.
Open Scope Z_scope.

Section C1Defs. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable RA_LLVMF : Z.
Local Abbreviation segs := decodesegsB0.
Local Abbreviation rd W mem := (mrestrict (w_H W) mem).

(* What the slot pre gives this segment: lib/B/Prog/LLVMFuzzerTestOneInput_segX_exit_defs.v ex_base's conclusions,
   and the read-only image view at entry (dec_b_rom). *)
Definition c1_pre (cx : dctx) : Prop :=
  YK0s.ret_ok (YK11.getr (d_regs cx) 1) /\ raZ (d_regs cx) = RA_LLVMF /\ 4096 <= RA_LLVMF /\
  YK11.getr (d_regs cx) 3 = w64 (as_gp B) /\ YK11.getr (d_regs cx) 4 = w64 (as_tp B) /\
  astk_ok DEC_LLVMF_STK (d_ly cx) (d_sp0 cx) /\
  @achain rc (d_ly cx) (aview segs (w_H (d_W cx)) (d_mem cx)) (d_sp0 cx) (s0Z (d_regs cx)) [] /\
  (d_n cx = 0 \/ In (d_p cx, d_n cx) (ablocks B (d_ly cx) (d_S cx))) /\
  0 <= d_n cx < 2 ^ 26 /\ d_n cx = Z.of_nat (length (d_pl cx)) /\
  st_nev (d_S cx) + DEC_EV_LIB <= EV_MAX /\ blocks_bytes (d_S cx) + DEC_LIVE_LIB <= LIVE_MAX /\
  dec_b_rom cx.

(* The state at a call of this stretch, at journal count k and meter spent / still available. *)
Definition c1_st (cx : dctx) (res out mode nch ns k spent rest : Z) (fx' : YK11.FPState)
    (ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
    (mem' : word -> option byte) (md' : Model) : Prop :=
  frm_zero (@fp_csr fx') /\
  dec_b_core B cx ly' S' W' regs' mem' md' k /\
  Permutation (ablocks B ly' S')
    (ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_b_len (d_n cx))] ++ [(out, dec_b_olen nch ns)]) /\
  4096 <= res /\ 4096 <= out /\
  mo_le MT (d_S cx) S' spent /\ mo_ok MT S' rest /\
  c1_mem cx W' mem' res out mode nch ns /\
  dec_b_slot cx (aview segs (w_H W') mem') 80 (res + 50).

(* The seven callee-saved registers every cut point of this stretch states: s3 the plain check (+0x5d4), s4 the
   length, s5 the mode, s7 the channel count, s8 fits0, s10 the buffer length, s11 the copy. *)
Definition c1_regs (cx : dctx) (res out mode nch ns : Z) (regs' : bvmap 5 word) : Prop :=
  YK11.getr regs' 19 = w64 (if CPlain.plain_ok (dec_b_len (d_n cx)) (d_body cx) nch ns then 1 else 0) /\
  YK11.getr regs' 20 = w64 (dec_b_len (d_n cx)) /\
  YK11.getr regs' 21 = w64 mode /\
  YK11.getr regs' 23 = w64 nch /\
  YK11.getr regs' 24 = w64 (dec_b_fits0 nch ns) /\
  YK11.getr regs' 26 = w64 (dec_b_olen nch ns) /\
  YK11.getr regs' 27 = w64 res.

(* From the call of check_round_trip at +0x68c (pc = its entry, ra = +0x690, a0..a3 = copy + 50, buffer, nch, ns). *)
Definition c1_K_crt : Prop :=
  forall cx (res out mode nch ns : Z) fx' ly' S' W' regs' mem' md',
  c1_pre cx ->
  c1_st cx res out mode nch ns dec_ev_5cc (dec_spent_5cc MT (d_n cx)) (dec_rest_5cc MT) fx' ly' S' W' regs' mem' md' ->
  c1_regs cx res out mode nch ns regs' ->
  CDec.decode_ok (dec_b_len (d_n cx)) (d_body cx) nch ns = true -> 0 < ns <= 12 ->
  garr8 segs (rd W' mem') out (map (fun b : byte => bv_unsigned b) (CDec.braid_out (d_body cx) nch ns)) ->
  YK11.getr regs' 22 = w64 out ->
  YK11.getr regs' 1 = w64 (DEC_A_LLVMF + 0x690) ->
  YK11.getr regs' 10 = w64 (res + 50) -> YK11.getr regs' 11 = w64 out ->
  YK11.getr regs' 12 = w64 nch -> YK11.getr regs' 13 = w64 ns ->
  SRr segs W' (@LeafCgKit.cfg_at fx' (decodeb_sigma DB_check_round_trip) regs' mem' md') (@llvm_b_st_6f0 rc B MT cx).

(* From the call of check_braid at +0x6bc (ra = +0x6c0, the same four arguments). *)
Definition c1_K_braid : Prop :=
  forall cx (res out mode nch ns : Z) fx' ly' S' W' regs' mem' md',
  c1_pre cx ->
  c1_st cx res out mode nch ns dec_ev_6f0 (dec_spent_6f0 MT (d_n cx)) (dec_rest_6f0 MT) fx' ly' S' W' regs' mem' md' ->
  c1_regs cx res out mode nch ns regs' ->
  CDec.decode_ok (dec_b_len (d_n cx)) (d_body cx) nch ns = true ->
  garr8 segs (rd W' mem') out (map (fun b : byte => bv_unsigned b) (CDec.braid_out (d_body cx) nch ns)) ->
  YK11.getr regs' 22 = w64 out ->
  YK11.getr regs' 1 = w64 (DEC_A_LLVMF + 0x6c0) ->
  YK11.getr regs' 10 = w64 (res + 50) -> YK11.getr regs' 11 = w64 out ->
  YK11.getr regs' 12 = w64 nch -> YK11.getr regs' 13 = w64 ns ->
  SRr segs W' (@LeafCgKit.cfg_at fx' (decodeb_sigma DB_check_braid) regs' mem' md') (@llvm_b_st_6f0 rc B MT cx).

(* From the call of __asan_memset at +0x6d4 (ra = +0x6d8, a0 = buffer, a1 = 0xa5, a2 = olen, s2 = buffer). *)
Definition c1_K_memset : Prop :=
  forall cx (res out mode nch ns : Z) fx' ly' S' W' regs' mem' md',
  c1_pre cx ->
  c1_st cx res out mode nch ns dec_ev_6f0 (dec_spent_6f0 MT (d_n cx)) (dec_rest_6f0 MT) fx' ly' S' W' regs' mem' md' ->
  c1_regs cx res out mode nch ns regs' ->
  YK11.getr regs' 18 = w64 out ->
  YK11.getr regs' 1 = w64 (DEC_A_LLVMF + 0x6d8) ->
  YK11.getr regs' 10 = w64 out -> YK11.getr regs' 11 = w64 DEC_FILL ->
  YK11.getr regs' 12 = w64 (dec_b_olen nch ns) ->
  SRr segs W' (@LeafCgKit.cfg_at fx' (decodeb_sigma DB___asan_memset) regs' mem' md') (@llvm_b_st_6f0 rc B MT cx).

(* The head's statement: from llvm_b_st_5cc to one of the three calls. *)
Definition c1_head_stmt : Prop :=
  c1_K_crt -> c1_K_braid -> c1_K_memset ->
  forall (cx : dctx) (W' : world segs) (c' : config),
  c1_pre cx -> @llvm_b_st_5cc rc B MT cx W' c' -> SRr segs W' c' (@llvm_b_st_6f0 rc B MT cx).
End C1Defs.
