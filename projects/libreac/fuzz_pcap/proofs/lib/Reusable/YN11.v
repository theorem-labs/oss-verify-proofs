(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN11.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0s YK0h YK0i YK14 YK1b YK1a YK15 YK0v YK02 YP0n YM06 YK1j YM00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP0m YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YH00 YH03 YH02.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO0i YO0f YO0g YO0h YO0w YO0s YO0x YO0z YO14 YO0v YO0q YO0u YO15 YO10 YO12 YO0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO0a YO0c YO0b YN01 YN03 YN02 YN2b YN2e YN0g YN0d YN0c YN25 YN0a YN0p YN2j YN2h YN2n YN2m YN2d YN2k YN0j YN0h YN0i YN1k YN2w YN1d YN31 YN0z YN12 YN1f YN19 YN1a YN00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Notation B := src0_msyms.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem src0_alloc_slot_of_parts_g : alloc_meta_hyp B -> (forall fuel, SEG_group_at fuel -> SEG_head_at fuel) -> SEG_mm -> SEG_nest -> alloc_slot_hyp_g B.
Proof.
intros AMH SH SM SN. pose proof ctx_owned_ok as CO. pose proof (alloc_slot_ind AMH SH SM SN NEST_FUEL NEST_FUEL (le_n _)) as IH.
unfold alloc_slot_hyp_g. intros L A regs mem md sc n g HW AMA BND RSV SPOK Hsc Hn Hfit MID AUXP PRE R10 R11 Hg.
assert (RX : rawX [] A) by (intros x []).
assert (Hstk : ASF <= AS_STACK <= AS_STACK) by (unfold ASF, AS_STACK, ALLOC_STACK; lia).
assert (HB : as_budget sc <= AS_STACK) by (pose proof (as_budget_range sc ltac:(lia)); unfold AS_STACK, ALLOC_STACK; lia).
assert (HN : (need sc <= NEST_FUEL)%nat) by (apply need_le_fuel; lia).
change (pc_alloc_slot (ms_pcs B)) with src0_A_alloc_slot. change (ms_segs B) with src0segs. change (ms_guard B) with GUARD. change (ms_guard B) with GUARD in Hg.
pose proof (IH [] U0 L A regs mem md sc n AS_STACK g HW RX AMA BND RSV SPOK Hsc Hn MID AUXP PRE Hstk R10 R11 Hg (fun k => eq_refl) HB HN) as M.
eapply mreal_mono; [| exact M]. cbv beta. intros r c' (L' & regs' & mem' & md' & Ec & MID' & AMA' & BND' & RSV' & SPOK' & LE & PRS & VM & FR & SCR & RA0 & UZ & AK & GD).
exists L', regs', mem', md'. repeat (split; [assumption|]). split; [| split; [exact SCR | split; [exact RA0 | split; [exact UZ | exact GD]]]].
intros x Hx No No' Nn Ns. apply (FR x Hx); try assumption. intros Hc. apply No. exact (CO U0 L A mem md x HW MID Hc).
Qed.
Theorem src0_alloc_slot_g : alloc_slot_hyp_g B.
Proof. exact (src0_alloc_slot_of_parts_g src0_alloc_meta (src0_SEG_head src0_alloc_meta) src0_SEG_mm (src0_SEG_nest_partial src0_alloc_meta src0_NEST_SUCC)). Qed.
End a.
