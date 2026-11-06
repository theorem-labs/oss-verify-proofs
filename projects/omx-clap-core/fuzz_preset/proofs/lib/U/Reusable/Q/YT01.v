(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/Q/YW0a.v, with its module paths and module names changed; 15 of its 38 lines of code are new or changed and 50 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0s YK15 YM06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YH00 YH03 YH02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YN03 YN2b.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition realloc_class_T (C : Z -> Prop) : Prop :=
forall pc L A regs mem md p nold n g am idx fr,
ms_realloc src0_msyms = Some pc ->
call_pre_k src0_msyms (MRx src0_msyms) REALLOC_STACK L A regs mem md ->
In (p, nold) (user_blocks A) ->
getr regs 10 = Z_to_bv 64 (ptr_addr L p) -> getr regs 11 = Z_to_bv 64 n ->
0 <= n < 2 ^ 62 ->
usedX [] A g am -> 0 <= idx <= am_last am -> ss_fr (nth_slot am idx) = Some fr -> fr_kind fr = FUser ->
fr_n fr = nold -> p = frame_ptr am idx fr -> C (am_sc am) ->
mreal (ms_segs src0_msyms) (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom (ms_segs src0_msyms))) md)
(realloc (Some p) n A)
(realloc_leaf src0_msyms (MRx src0_msyms) L A regs mem md p nold n).
Definition realloc_small_T : Prop := realloc_class_T (fun sc => sc < 48).
Definition realloc_k3b_T : Prop := realloc_class_T (fun sc => sc = 63).
Theorem realloc_by_class : realloc_small_T -> realloc_k3b_T -> realloc_realizes src0_msyms (MRx src0_msyms).
Proof using.
intros SM K3 pc L A regs mem md p nold n Hpc PRE Hin H10 H11 Hn.
assert (HW : WF A) by (destruct PRE as (_ & HW & _); exact HW).
destruct (user_blocks_frame A p nold HW Hin) as (g & am & idx & fr & Hu & Hidx & Hfr & Hk & Hn' & Hp).
destruct (@inv_groups [] None U0 A HW g am Hu) as (_ & _ & _ & Hc & _).
destruct Hc as [(H63 & _) | ((_ & Hlt) & _)].
- exact (K3 pc L A regs mem md p nold n g am idx fr Hpc PRE Hin H10 H11 Hn Hu Hidx Hfr Hk Hn' Hp H63).
- exact (SM pc L A regs mem md p nold n g am idx fr Hpc PRE Hin H10 H11 Hn Hu Hidx Hfr Hk Hn' Hp Hlt).
Qed.
End a.
