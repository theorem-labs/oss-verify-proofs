(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/YCfi.v (link_SMP, link_FFL, link_ASF)
   and the class-0 side stack lib/B/Rt/StackMalloc0.v (relocated from fuzz_grant's image B, a working branch
   cce7df57aaa6), at libreac/fuzz_decode's ASan+UBSan record TfibB (lib/B/YD2l.v). *)
(* Five hypotheses of lib/B/DecodeBClose.v, each proved at image B's concrete record TfibB and segments decodesegsB0
   with DecodeBClose.v's own text (its `segs` is decodesegsB0, its `B` is TfibB; the names resolve to the same modules,
   Reusable/YG0d.v and Reusable/YCbq.v, under the same local float-state instance YK11.fx0):
     H_RT_STACK_MALLOC0  (DecodeBClose.v:238)  dec_rt_stack_malloc0
     HB_PC_STACK_MALLOC0 (DecodeBClose.v:314)  dec_pc_stack_malloc0
     HB_SMP              (DecodeBClose.v:346)  dec_smp
     HB_ASF              (DecodeBClose.v:348)  dec_asf
     HB_FFL              (DecodeBClose.v:350)  dec_ffl *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YM05 YK04 YA0i YA0n YG00 YG01 YG05 YG0f YG0n YG0d YG0t YG0q YCbq.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBAddr.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YD2l.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require YCeg.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Rt Require StackMalloc0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Module SM0 := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Rt.StackMalloc0.
Module BCeg := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.YCeg.

(* H_RT_STACK_MALLOC0: the class-0 walk at decode B's __asan_stack_malloc_0 (0x3c6fc), from AR_laws_ok
   (Reusable/YG0q.v) and TfibB_syms (lib/B/YD2l.v). *)
Lemma dec_rt_stack_malloc0 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @astack_malloc_realizes fx rc decodesegsB0 TfibB 0.
Proof.
  intros rc fx. apply SM0.stack_malloc0_contract; [apply AR_laws_ok | exact TfibB_syms].
Qed.

(* HB_PC_STACK_MALLOC0: lib/B/YF0l.v Tfib_code's class-0 entry is the listing's __asan_stack_malloc_0
   (lib/B/Prog/DecodeBAddr.v), both 0x3c6fc. *)
Lemma dec_pc_stack_malloc0 : pc_stack_malloc (as_code TfibB) 0 = decodeb_sigma DB___asan_stack_malloc_0.
Proof. vm_compute. reflexivity. Qed.

(* HB_SMP: cgif lib/YCfi.v link_SMP, from Reusable/YG05.v stack_malloc_progress. *)
Lemma dec_smp : stack_malloc_progressP TfibB.
Proof. intros s cid W Hc Hn. exact (stack_malloc_progress (as_universe TfibB) s cid W Hc Hn). Qed.

(* HB_ASF: cgif lib/YCfi.v link_ASF, from Reusable/YG0t.v astack_free_law_ok. *)
Lemma dec_asf : forall (rc : YM05.RunCeil), astack_free_law decodesegsB0 TfibB.
Proof. intros rc. exact (astack_free_law_ok decodesegsB0 TfibB). Qed.

(* HB_FFL: cgif lib/YCfi.v link_FFL, from AR_laws's al_flag and al_client_img and image B's cover
   (lib/B/YCeg.v tfib_img_cover: the ledger's image covers 0x10000 .. 0x5f6000, the two bounds Reusable/YCbq.v's
   off_img reads from Reusable/YImgTop.v). *)
Lemma dec_ffl : forall (rc : YM05.RunCeil), frame_flag_lawP decodesegsB0 TfibB.
Proof.
  intros rc ly S W mem md cid pos HAR Hin.
  pose proof (AR_laws_ok decodesegsB0 TfibB) as LAWS.
  destruct (al_flag _ _ LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
  destruct (al_client_img _ _ LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
  { right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
  pose proof HAR as (M & L & _). pose proof (BCeg.tfib_img_cover ly S md L) as [C1 C2].
  unfold BCeg.TFIB_IMG_LO, BCeg.TFIB_IMG_END in C1, C2.
  destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
  split; [exact Hp|]. split; [exact Ho|]. split.
  - split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
  - split; [exact H4096|]. split; [|exact Hceil]. unfold zone2, off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
