(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YN03.v, with its module paths and module names changed; 425 of its 462 lines of code are new or changed and 499 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/AllocCut.v, with its module paths changed; 25 of its 58 lines of code are new or changed and 429 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YK11 YK0s YK0i YK15 YM06 YM06_cf YM05 YM02 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import
YO0i YO0f YO0g YO0q YO0x YO0d YO0e YO05 YO02 YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO16 YL01.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YO10 YO0s YO0u YO15 YN03 YN2b YN33.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YO0d_cf YO03_cf YO0n_cf YH02 YN09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import AllocSI AllocGS AllocCount AllocBound AllocDepth AllocFree AllocMalloc AllocRealloc.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import AllocMB AllocMallocMB AllocFreeMB AllocReallocMB AllocMallocPath AllocFreePath.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import Contract AllocSlots AllocCut SlotAgree ZAllocator AllocCf SlotAgreeI.
Import ListNotations.
Local Open Scope Z_scope.

(* free_contract_cfi from the cut-free free realization, for any allocator API: the proof of AllocCf.free_contract_cf_ok
   with the resource fact cut down to II (free keeps II: OK4_free's post FPost). *)

Section A. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section W.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Theorem free_contract_cfi_ok : AllocExtra B MR -> ro_apart_b B = true -> free_realizes_cf B MR ->
  free_contract_cfi B API.
Proof using.
intros AX HB HFcf L A regs mem md p n Hpre Hro Hin Hp HII T HK.
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
pose proof (free_reqs_ok A p n HW Hin) as RQ.
pose proof (OK4_free (Some p) A RQ HII) as [HOK HLV].
pose proof (mreal_cf_SR_cfv segs (free (Some p) A) _ _ (HFcf L A regs mem md p n Hpre Hin Hp)
  (free_safe A p n HW Hin) HOK (r_free (Some p) (vml (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom segs)) md)) A)) as HS.
apply (SR_cfv_crealizes segs _ _ T HS). intros c' Hc'. apply HK. clear HS HK T.
destruct Hc' as ([[] A'] & tr & Hcp & HL).
assert (HII' : II A').
{ pose proof (leaves_cpath04 _ _ _ _ HLV Hcp) as HP. unfold FPost in HP. cbn [snd] in HP. exact (proj1 HP). }
destruct HL as (L' & regs' & mem' & md' & -> & Hpost & (l1 & l2 & E1 & E2)).
pose proof Hpre as (HMR0 & _ & _ & _ & _ & Hsp & _).
cbn [fst snd] in *.
assert (Hsub : forall q k, In (q, k) (user_blocks A) -> q <> p -> In (q, k) (user_blocks A')).
{ intros q k Hq Hne. rewrite E1 in Hq. rewrite E2. apply in_app_iff in Hq as [Hq|[Hq|Hq]]; apply in_app_iff;
[left; exact Hq | injection Hq as -> _; exfalso; exact (Hne eq_refl) | right; exact Hq]. }
pose proof Hpost as (HMR & _ & _ & _ & Hstab & _ & _ & _ & Hkeep & _).
pose proof (proj1 (call_post_k_alloc B MR L A regs mem md _ L' A' regs' mem' md') Hpost) as Hpk.
exists L', A', regs', mem', md'. split; [reflexivity|]. split; [exact Hpost|].
split; [exact (blocks_del L L' A A' p n l1 l2 Hstab E1 E2)|].
split.
{ apply (kept_of_post B L A A' mem mem'); [exact Hkeep|]. intros q k Hq Hg. apply Hsub; [exact Hq|]. intros ->. exact (Hg eq_refl). }
split; [exact (ro_agree_post B MR ALLOC_STACK L A regs mem md _ L' A' regs' mem' md' AX HB Hsp HMR0
(fun a Ha => ex_intro _ p (ex_intro _ n (conj Hin Ha))) Hpk Hro)|].
split; [exact (guard_kept_post B MR L A mem md L' A' mem' md' AX HMR0 HMR)|].
split; [exact Hsub|].
split; [intros Hd; exact (free_keeps_init_done (Some p) A tr tt A' Hd (cpath04_yields _ _ _ Hcp))|].
split; [exact (regions_grow_free A p n tr A' HW Hin Hcp)|].
exact HII'.
Qed.

End W.

Theorem zlib_free_contract_cfi : free_contract_cfi src0_msyms zlib_API.
Proof using.
  exact (free_contract_cfi_ok src0_msyms zlib_API zlib_allocator_extra ltac:(vm_compute; reflexivity) src0_free_realizes_cf).
Qed.

End A.
