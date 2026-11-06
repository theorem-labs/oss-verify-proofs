(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset image A (asan, pin 1be0f53d96cb), the two parameters at which the
   image-A malloc interceptor walk discharges a Theorem Labs lane's Record wrap_malloc_walk_cf (lib/Reusable/YGcfMallocCompose.v
   :149, blob e929a4c12d5b):
   - ARXh_A, the allocator relation: the exact text of YGcfDIface.ARXs_cf (YGcfDIface.v:73-77 at the base, already
     indexed by the ghost set Hp), at the segments tfibsegs. Isolated here so that the swap to AIfaceSA's ARXs_A
     (AllocReloc's alloc8, a Theorem Labs lane) is a one-line change; ARXh_A_ARXs_cf below states that it IS ARXs_cf.
   - K_A, the invariant from the call segment (WrapMallocACall.seg_call) to the return segment (WrapMallocARet):
     what asan_malloc's and the interceptor's epilogues read at Allocate's return, i.e. the stack pointer and return
     address at Allocate's entry, the callee-saved registers the call segment keeps (gp, tp, s6..s11, and s0 = the
     caller's sp), asan_malloc's frame (saved s0, ra = RA_ASAN_MALLOC), the interceptor's frame (the caller's ra,
     s0..s5 at sp - 8 .. sp - 56) and the caller's stack window present. The world is the caller's (no model step). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocCompose YGcfDIface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v WrapMallocAConsts.
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope Z_scope.

Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable B : asyms.

(* YGcfDIface.v:73-77 at the OLD base, ARXs_cf's body, at tfibsegs. On the #102 base ARXs_cf drops the last conjunct
   xs_placed_cf, which ARcf now implies (ARmcf's last field amc_xs_placed, YG0ncf.xs_placed_of_ARcf), so the two
   relations are still equivalent (ARXh_A_ARXs_cf). *)
Definition ARXh_A : YGcfMallocCompose.ARXh_t tfibsegs := fun Hp inst ly S W mem md =>
inst = as_inst B /\ ARcf tfibsegs B ly S Hp W mem md /\
qmeter_cf S /\ Z.of_nat (length (st_sec_arr S)) < cf_sec_live_max /\ ERRB_ROOM S /\
abudget_cf S + FA_GROW_MAX + FA_GROW_MAX / 8 <= CF_MAX /\ batch_room_cf S /\ xs_placed_cf ly S.

Lemma ARXh_A_ARXs_cf : forall {IM : ImgBase.AImg} {DI : ImgBaseDG.DImg} Hp inst ly S W mem md,
ARXh_A Hp inst ly S W mem md <-> YGcfDIface.ARXs_cf B tfibsegs Hp inst ly S W mem md.
Proof.
intros IM DI Hp inst ly S W mem md. unfold ARXh_A, YGcfDIface.ARXs_cf. split.
- intros (Hi & AR & Q & L & E & Bd & Br & _). exact (conj Hi (conj AR (conj Q (conj L (conj E (conj Bd Br)))))).
- intros (Hi & AR & Q & L & E & Bd & Br).
  exact (conj Hi (conj AR (conj Q (conj L (conj E (conj Bd (conj Br (xs_placed_of_ARcf tfibsegs B ly S Hp W mem md AR)))))))).
Qed.

Definition K_A : YGcfMallocCompose.Kmalloc_t tfibsegs := fun ly S Hp W regs mem md n ch W1 regsA memA mdA =>
W1 = W /\ getr regsA 2 = w64 (spZ regs - 2144) /\ getr regsA 1 = w64 RA_ALLOC /\
getr regsA 8 = getr regs 2 /\ getr regsA 3 = getr regs 3 /\ getr regsA 4 = getr regs 4 /\
(forall r : Z, 22 <= r <= 27 -> getr regsA (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (spZ regs - 2144) 8 (spZ regs) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (spZ regs - 2136) 8 RA_ASAN_MALLOC /\
val_mem tfibsegs (mrestrict (w_H W) memA) (spZ regs - 8) 8 (raZ regs) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (spZ regs - 16) 8 (s0Z regs) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (spZ regs - 48) 8 (bv_unsigned (getr regs 20)) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (spZ regs - 56) 8 (bv_unsigned (getr regs 21)) /\
(forall a, spZ regs - ASTACK <= a < spZ regs -> apresent (w_H W) memA a).
End G.
