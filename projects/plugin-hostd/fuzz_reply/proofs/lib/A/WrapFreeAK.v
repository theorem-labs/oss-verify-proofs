(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: relocated to plugin-hostd/fuzz_reply's asan image A (pin 42c58610e125, unstripped twin d751b179ea49) from proofs/omx-clap-core/fuzz_preset/lib/A/WrapFreeAK.v at f6c2b01c2457 (image A' p102) by alreloc a5c53bb2bed4 (every image numeral by symbol + offset; hand check a Theorem Labs lane's RELOC-CHECK.md (sha256 6283be15fb26; internal record)); module paths changed (lib.Reusable -> lib.A for YGcfMallocCompose); K_A renamed K_reply. *)
(* Theorem Labs, 2026-10: RELOCATED to the #102 pins (image A' = asan 1be0f53d96cb, twin bff8519bbe3e) from a working branch cb44bc9b99c (old-pin image A) by the relocation script reloc_A2.py (named with its outputs in the commit that added this line): every code address moved by symbol + offset (reloc_A2.out), the walk's functions checked by bytecmp 1480ca2faea0 + a target pass (measure_A2.out); data addresses come by name from int102's A' tables; ARXs_cf / ARmcf follow a Theorem Labs lane's a2b14794b6e6 (xs_placed is ARmcf's field amc_xs_placed). *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset image A' (#102 asan, pin 1be0f53d96cb, twin bff8519bbe3e): K_reply (K_A), the
   invariant of a Theorem Labs lane's Record wrap_free_walk_cf (lib/Reusable/YGcfMallocCompose.v:334-336 Kfree_t) that the
   call segment (WrapFreeACall.v, field wf_call) hands to the return segment (WrapFreeARet.v, field wf_ret).
   It carries what ___interceptor_free's epilogue (0x53f9c-0x53fc0) reads: the stack pointer and the return address
   at Deallocate's entry (asan_free tail-jumps to Deallocate, so Deallocate returns to 0x53f9c, after
   `jal asan_free` at 0x53f98), the callee-saved registers the call segment keeps, the six saved registers and ra in
   the interceptor's frame (sd at 0x53df8-0x53e10, at sp - 8 .. sp - 56 of the caller's sp), and the caller's stack
   window present. The world is the caller's (no model step in the call segment). Image A numerals: 2128 =
   0x7f0 + 0x60 (the frame), 0x53f9c (= ___interceptor_free + 0x1a8). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfMallocCompose.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

Definition K_reply : Kfree_t tfibsegs := fun ly S Hp W regs mem md p n ch W1 regsD memD mdD =>
W1 = W /\ getr regsD 2 = w64 (spZ regs - 2128) /\ getr regsD 1 = w64 0x53f9c /\
getr regsD 3 = getr regs 3 /\ getr regsD 4 = getr regs 4 /\
(forall r : Z, 22 <= r <= 27 -> getr regsD (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
val_mem tfibsegs (mrestrict (w_H W) memD) (spZ regs - 8) 8 (raZ regs) /\
val_mem tfibsegs (mrestrict (w_H W) memD) (spZ regs - 16) 8 (s0Z regs) /\
val_mem tfibsegs (mrestrict (w_H W) memD) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) /\
val_mem tfibsegs (mrestrict (w_H W) memD) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) /\
val_mem tfibsegs (mrestrict (w_H W) memD) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) /\
val_mem tfibsegs (mrestrict (w_H W) memD) (spZ regs - 48) 8 (bv_unsigned (getr regs 20)) /\
val_mem tfibsegs (mrestrict (w_H W) memD) (spZ regs - 56) 8 (bv_unsigned (getr regs 21)) /\
(forall a, spZ regs - ASTACK <= a < spZ regs -> apresent (w_H W) memD a).

End c.
