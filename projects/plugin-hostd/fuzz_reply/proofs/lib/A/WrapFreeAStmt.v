(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: relocated to plugin-hostd/fuzz_reply's asan image A (pin 42c58610e125, unstripped twin d751b179ea49) from proofs/omx-clap-core/fuzz_preset/lib/A/WrapFreeAStmt.v at f6c2b01c2457 (image A' p102) by alreloc a5c53bb2bed4 (no numeral here; hand check a Theorem Labs lane's RELOC-CHECK.md (sha256 6283be15fb26; internal record)); module paths changed (lib.Reusable -> lib.A for AllocG DeallocG RGtop YGcfRmodel YGcfMallocCompose); the round-3 texts of fu1 b70f01ca629f. *)
(* Theorem Labs, 2026-10: RELOCATED to the #102 pins (image A' = asan 1be0f53d96cb, twin bff8519bbe3e) from a working branch cb44bc9b99c (old-pin image A) by the relocation script reloc_A2.py (named with its outputs in the commit that added this line): every code address moved by symbol + offset (reloc_A2.out), the walk's functions checked by bytecmp 1480ca2faea0 + a target pass (measure_A2.out); data addresses come by name from int102's A' tables; ARXs_cf / ARmcf follow a Theorem Labs lane's a2b14794b6e6 (xs_placed is ARmcf's field amc_xs_placed). *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset, the free interceptor walk of image A' (#102 asan, stripped pin
   1be0f53d96cb, unstripped twin bff8519bbe3e) over the second allocator instance ARcf: the two named texts the walk
   needs beside a Theorem Labs lane's Record wrap_free_walk_cf (lib/Reusable/YGcfMallocCompose.v:338-367, sha256 c6515cb7094c (internal record), at
   a working branch 8c3f5f4b9e79).
   - wf_call_stmt_FIX fr: field wf_call (YGcfMallocCompose.v:342-350) verbatim with ONE premise added,
     ly_bot ly + fr < spZ regs, fr the bytes the interceptor puts below the caller's sp before Deallocate's entry.
     dealloc_pre asks ly_bot ly < spZ regsD (DeallocG.v:83); on image A spZ regsD = spZ regs - 2128
     (___interceptor_free's frame, 0x7f0 + 0x60; asan_free has none), and acall_pre_cf gives only ly_bot ly < spZ regs
     (YG0dcf.v:52). Reported to a Theorem Labs lane 14:4xZ (same gap as a Theorem Labs lane's malloc twin); a8 15:35Z: the premise stays
     NAMED until a Theorem Labs lane's AcallPrefix change gives acall_pre_cf `ly_bot ly + ACALL_PREFIX < spZ regs`
     (ACALL_PREFIX >= 2144 > 2128), which discharges it.
   No image constant and no function is proved here (rule 24); the walk is WrapFreeA*.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AllocG DeallocG RGtop YGcfRmodel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG03cf YAkMemnorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfMallocCompose.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

Section J.
Variable segs : list Segment.
Variable B : asyms.

Section F.
Variable atpD : Z.

(* F1, YGcfMallocCompose.v:342-350, with `ly_bot ly + fr < spZ regs` added after its two premises. *)
Definition wf_call_stmt_FIX (fr : Z) (ARX : ARXh_t segs) (K : Kfree_t segs) : Prop :=
forall ly S Hp W regs mem md p n ch,
  fentry_cf segs B ly S Hp W regs mem md p n ch -> rpreD_free_cf B (finit_cf S) n -> ly_bot ly + fr < spZ regs ->
  SRr segs W (cfg_at segs (pc_wrap_free (as_code B)) regs mem md)
  (fun W1 c1 => exists inst so bp regsD memD mdD,
    c1 = cfg_at segs cf_pc_deallocate regsD memD mdD /\
    free_dpre_cf segs B atpD ARX Hp inst so bp ly (finit_cf S) W1 regsD memD mdD p n (ftr_cf B ly regs ch) /\
    same_io md mdD /\ RGtop.rin regs (spZ regsD) DeallocG.DFSTACK_G /\
    ikeep_cf segs B ly S regs W mem W1 memD /\ errno_kept_cf B mem memD /\
    K ly S Hp W regs mem md p n ch W1 regsD memD mdD).
End F.
End J.
End G.
