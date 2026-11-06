(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_decode's ASan image (rule 24: no function proved; this
   file is assembly). It discharges five Section hypotheses of lib/A/DecodeClose.v at the core's concrete symbol record
   GrantB (lib/A/AD2l.v GrantB, GrantB_syms). Each lemma states its hypothesis with DecodeClose.v's text at B := GrantB:
   - dec_rt_stack_malloc0 = H_RT_STACK_MALLOC0 (DecodeClose.v:244): lib/A/Rt/StackMalloc0.v stack_malloc0_contract,
     a Theorem Labs lane's class-0 walk (a working branch 8595c26c630 proofs/libreac/fuzz_grant/lib/A/Rt/StackMalloc0.v; SHARED-WALKS
     row 'stack_malloc 0 (cgif-AR units)') relocated to fuzz_decode.asan, at Reusable/YG0q.v AR_laws_ok and GrantB_syms;
   - dec_pc_stack_malloc0 = HB_PC_STACK_MALLOC0 (:320): by computation. lib/A/AF0l.v Tfib_code's pc_stack_malloc 0 and
     lib/A/Prog/DecodeAddr.v decode_sigma DS___asan_stack_malloc_0 are both __asan_stack_malloc_0 (size 372) of
     fuzz_decode.asan, the only class the image's pc_stack_malloc names;
   - dec_smp = HB_SMP (:352): Reusable/YG05.v stack_malloc_progress at GrantB's universe (cgif lib/A/ACfi.v link_SMP);
   - dec_asf = HB_ASF (:354): Reusable/YG0t.v astack_free_law_ok (cgif lib/A/ACfi.v link_ASF);
   - dec_ffl = HB_FFL (:356): AR_laws's al_flag and al_client_img with the image cover lib/A/ACeg.v tfib_img_cover; the
     proof is cgif lib/A/ACfi.v link_FFL's, unchanged. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YM05 YK04 YA0i YA0n YG00 YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YG05 YG0t.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import DecodeSyms DecodeAddr.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require AD2l ACeg.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Rt Require StackMalloc0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
(* As lib/A/DecodeClose.v states its hypotheses: the same float-state instance and the same segment list. *)
#[local] Existing Instance YK11.fx0.
Local Notation segs := decodesegs0.
Local Notation GrantB := AD2l.GrantB.

Lemma dec_rt_stack_malloc0 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @astack_malloc_realizes fx rc segs GrantB 0.
Proof.
  intros rc fx. exact (StackMalloc0.stack_malloc0_contract GrantB (AR_laws_ok segs GrantB) AD2l.GrantB_syms).
Qed.

Lemma dec_pc_stack_malloc0 : pc_stack_malloc (as_code GrantB) 0 = decode_sigma DS___asan_stack_malloc_0.
Proof. reflexivity. Qed.

Lemma dec_smp : stack_malloc_progressP GrantB.
Proof. intros s cid W Hc Hn. exact (YG05.stack_malloc_progress (as_universe GrantB) s cid W Hc Hn). Qed.

Lemma dec_asf : forall (rc : YM05.RunCeil), astack_free_law segs GrantB.
Proof. intros rc. exact (YG0t.astack_free_law_ok (rc := rc) segs GrantB). Qed.

Lemma dec_ffl : forall (rc : YM05.RunCeil), frame_flag_lawP segs GrantB.
Proof.
intros rc ly S W mem md cid pos HAR Hin.
pose proof (AR_laws_ok segs GrantB) as LAWS.
destruct (al_flag _ _ LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
destruct (al_client_img _ _ LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof HAR as (M & L & _). pose proof (ACeg.tfib_img_cover ly S md L) as [C1 C2].
unfold ACeg.TFIB_IMG_LO, ACeg.TFIB_IMG_END in C1, C2.
destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
split; [exact Hp|]. split; [exact Ho|]. split.
- split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
- split; [exact H4096|]. split; [|exact Hceil]. unfold zone2, off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

Print Assumptions dec_rt_stack_malloc0.
Print Assumptions dec_pc_stack_malloc0.
Print Assumptions dec_smp.
Print Assumptions dec_asf.
Print Assumptions dec_ffl.
