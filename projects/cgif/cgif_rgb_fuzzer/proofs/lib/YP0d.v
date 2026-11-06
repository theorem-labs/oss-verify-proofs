(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0s YK0j YK15 YN06 YN02 YQ0b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0u YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : malloc_syms.
Variable MR : MR_t.
Let segs := ms_segs B.
Theorem realloc_SR :
realloc_realizes B MR ->
forall pc L A regs mem md p nold n,
ms_realloc B = Some pc ->
call_pre_k B MR REALLOC_STACK L A regs mem md ->
In (p, nold) (user_blocks A) ->
getr regs 10 = Z_to_bv 64 (ptr_addr L p) -> getr regs 11 = Z_to_bv 64 n ->
MMAP_THRESHOLD <= n -> MMAP_THRESHOLD < nold -> nold + PGSZ <= n < 2 ^ 62 ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
(fun c' => exists r tr, cpath (realloc (Some p) n A) tr r /\ realloc_leaf B MR L A regs mem md p nold n r c').
Proof.
intros HR pc L A regs mem md p nold n Hpc Hpre Hin Hp Hn Hth Hbig Hrange.
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
apply (mreal_SR segs _ _ _ (HR pc L A regs mem md p nold n Hpc Hpre Hin Hp Hn Hth Hbig Hrange)).
eapply realloc_safe; [exact HW | exact Hin | exact Hth | lia].
Qed.
End d.
Section e.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.
Hypothesis REALLOC : realloc_realizes B MR.

End e.
End c.
