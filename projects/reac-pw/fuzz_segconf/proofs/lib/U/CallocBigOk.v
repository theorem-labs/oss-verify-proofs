(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YN03.v, with its module paths and module names changed; 426 of its 462 lines of code are new or changed and 500 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/AllocCut.v, with its module paths and module names changed; 51 of its 124 lines of code are new or changed and 389 lines of the source are left out. *)
(* segconf's calloc contracts (UBSan build) with no 4096-byte cap (CallocBigC.v), from the certificates of CallocBig.v and
   CallocBig_cf.v. calloc_contract_big_ok is AllocCut.calloc_contract_ok (this frame, lines 349-389) with the
   certificate as a premise in place of aa_calloc (this frame's ms_calloc is None) and the cap raised;
   calloc_contract_big_cf_ok is libreac/fuzz_knock's AllocCallocCf.calloc_contract_cf_ok (25e3d17bdb50, lines 49-94)
   changed the same way, with the room proof of this frame's AllocCf.malloc_contract_cf_ok (it adds slotW). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YK11 YK0s YK0i YK15 YM06 YM06_cf YM05 YM02 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import
YO0i YO0f YO0g YO0q YO0x YO0d YO0e YO05 YO02 YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO16 YL01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YO10 YO0s YO0u YO15 YN03 YN2b YN33.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YO0d_cf YO03_cf YO0n_cf YH02 YN09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import PlaceCap.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import AllocSI AllocGS AllocCount AllocBound AllocDepth AllocFree AllocMalloc AllocRealloc.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import AllocMB AllocMallocMB AllocFreeMB AllocReallocMB AllocMallocPath AllocFreePath.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Contract AllocSlots AllocCut SlotAgree ZAllocator AllocUnif AllocCf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import AllocRoomW.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import CallocBigC CallocBig CallocBig_cf.
Import ListNotations.
Local Open Scope Z_scope.

Section A. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Section W.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Theorem calloc_contract_big_ok : AllocExtra B MR -> ro_apart_b B = true -> forall pc,
  calloc_realizes_big B MR pc -> calloc_contract_big B API pc.
Proof using.
intros AX HB pc HCR L A regs mem md m n b Hpre Hro Hm Hn Hrm Hrn Hsm HR HRm.
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
pose proof Hpre as (HMR0 & _ & _ & _ & _ & Hsp & _).
eapply SR_mono.
{ apply (mreal_SR04 segs _ _ _ (HCR L A regs mem md m n Hpre Hm Hn Hrm Hrn Hsm Hro)).
- apply malloc_safe; [exact HW | nia].
- exact (malloc_slots_ok04 A b (m * n) HW HR HRm). }
intros c' ([r A'] & tr & Hp & HL).
destruct (malloc_slots_step A b (m * n) tr r A' HW HR HRm Hp) as [[q ->] HRA'].
destruct HL as (L' & regs' & mem' & md' & -> & Hpost & Ha0 & Hnz & (l1 & l2 & E1 & E2) & Hz). cbn [fst snd] in *.
assert (Hin : In (q, m * n) (user_blocks A')) by (rewrite E1; apply in_app_iff; right; left; reflexivity).
assert (Hsub : forall p k, In (p, k) (user_blocks A) -> In (p, k) (user_blocks A')).
{ intros p k Hq. rewrite E2 in Hq. rewrite E1. apply in_app_iff in Hq as [Hq|Hq]; apply in_app_iff;
[left; exact Hq | right; right; exact Hq]. }
pose proof Hpost as (HMR & HW' & _ & _ & Hstab & _ & _ & _ & Hkeep & _).
split.
- unfold malloc_ret. exists L', A', regs', mem', md', (ptr_addr L' q).
split; [reflexivity|]. split; [exact Hpost|]. split; [exact Ha0|]. split; [exact Hnz|].
split; [exact (mr_blocks_aligned B MR (aa_laws API) _ _ _ _ _ _ HMR Hin)|].
split.
{ destruct (mr_blocks_range B MR (aa_laws API) _ _ _ _ _ _ HMR Hin) as [R1 R2].
split; [exact R1|]. split; [exact R2|]. intros i Hi. exact (ax_blocks_img AX _ _ _ _ _ _ i HMR Hin Hi). }
split; [exact (blocks_add L L' A A' q (m * n) l1 l2 Hstab E1 E2)|].
split; [apply (kept_of_post B L A A' mem mem'); [exact Hkeep | intros p k Hq _; exact (Hsub p k Hq)]|].
split; [exact (ro_agree_post B MR CALLOC_STACK L A regs mem md _ L' A' regs' mem' md' AX HB Hsp HMR0
(fun a (F : False) => match F with end) Hpost Hro)|].
split; [exact (guard_kept_post B MR L A mem md L' A' mem' md' AX HMR0 HMR)|].
split; [exact Hsub|].
split; [exact (YI04.init_done_of_block A' (q, m * n) HW' Hin)|].
split; [exact (regions_grow_malloc A (m * n) tr (Some q) A' HW ltac:(nia) Hp)|].
exact HRA'.
- exists (mkst regs' (getr regs 1) mem' (seg_rom segs)), md'. split; [reflexivity|].
intros i Hi. cbn [ms_mem ms_regs mkst]. rewrite Ha0.
pose proof alloc_ceiling_lt as AC.
assert (Hq : 4096 <= ptr_addr L' q /\ ptr_addr L' q + m * n <= alloc_ceiling)
by exact (mr_blocks_range B MR (aa_laws API) _ _ _ _ _ _ HMR Hin).
rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
apply Hz. exact Hi.
Qed.

Theorem calloc_contract_big_cf_ok : AllocExtra B MR -> ro_apart_b B = true -> forall pc,
  calloc_realizes_big_cf B MR pc -> calloc_contract_big_cf B API pc.
Proof using.
intros AX HB pc HCcf L A regs mem md m n b Hpre Hro Hm Hn Hrm Hrn Hsm HR HRc T HK.
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
pose proof Hpre as (HMR0 & _ & _ & _ & _ & Hsp & _).
pose proof HRc as [HRm _].
assert (Hn0 : 0 <= m * n) by nia.
assert (Hroom : roomcf (vm_limit (m_vmmaps md)) (malloc (m * n) A)).
{ apply roomcf_malloc; [apply malloc_reqs_ok; [exact HW | exact Hn0] | exact (proj1 HR) | exact Hn0 |
    exact (slots_room4 A b (m * n) HW HR HRm) | exact (room_cf_peak A b (m * n) md HW HR HRc) |].
  intros HL. exact (slotW_malloc A (m * n) (slots_slotW A b (m * n) md HW HR HRc HL)). }
refine (mreal_cf_SRcf B (malloc (m * n) A) _ _ (HCcf L A regs mem md m n Hpre Hm Hn Hrm Hrn Hsm Hro)
  (malloc_safe A (m * n) HW Hn0) (malloc_slots_ok04 A b (m * n) HW HR HRm) Hroom T _).
intros c' Hc'. apply HK. clear HK T.
destruct Hc' as ([r A'] & tr & Hp & HL).
destruct (malloc_slots_step A b (m * n) tr r A' HW HR HRm Hp) as [[q ->] HRA'].
destruct HL as (L' & regs' & mem' & md' & -> & Hpost & Ha0 & Hnz & (l1 & l2 & E1 & E2) & Hz). cbn [fst snd] in *.
assert (Hin : In (q, m * n) (user_blocks A')) by (rewrite E1; apply in_app_iff; right; left; reflexivity).
assert (Hsub : forall p k, In (p, k) (user_blocks A) -> In (p, k) (user_blocks A')).
{ intros p k Hq. rewrite E2 in Hq. rewrite E1. apply in_app_iff in Hq as [Hq|Hq]; apply in_app_iff;
[left; exact Hq | right; right; exact Hq]. }
pose proof Hpost as (HMR & HW' & _ & _ & Hstab & _ & _ & _ & Hkeep & _).
split.
- unfold malloc_ret. exists L', A', regs', mem', md', (ptr_addr L' q).
split; [reflexivity|]. split; [exact Hpost|]. split; [exact Ha0|]. split; [exact Hnz|].
split; [exact (mr_blocks_aligned B MR (aa_laws API) _ _ _ _ _ _ HMR Hin)|].
split.
{ destruct (mr_blocks_range B MR (aa_laws API) _ _ _ _ _ _ HMR Hin) as [R1 R2].
split; [exact R1|]. split; [exact R2|]. intros i Hi. exact (ax_blocks_img AX _ _ _ _ _ _ i HMR Hin Hi). }
split; [exact (blocks_add L L' A A' q (m * n) l1 l2 Hstab E1 E2)|].
split; [apply (kept_of_post B L A A' mem mem'); [exact Hkeep | intros p k Hq _; exact (Hsub p k Hq)]|].
split; [exact (ro_agree_post B MR CALLOC_STACK L A regs mem md _ L' A' regs' mem' md' AX HB Hsp HMR0
(fun a (F : False) => match F with end) Hpost Hro)|].
split; [exact (guard_kept_post B MR L A mem md L' A' mem' md' AX HMR0 HMR)|].
split; [exact Hsub|].
split; [exact (YI04.init_done_of_block A' (q, m * n) HW' Hin)|].
split; [exact (regions_grow_malloc A (m * n) tr (Some q) A' HW ltac:(nia) Hp)|].
exact HRA'.
- exists (mkst regs' (getr regs 1) mem' (seg_rom segs)), md'. split; [reflexivity|].
intros i Hi. cbn [ms_mem ms_regs mkst]. rewrite Ha0.
pose proof alloc_ceiling_lt as AC.
assert (Hq : 4096 <= ptr_addr L' q /\ ptr_addr L' q + m * n <= alloc_ceiling)
by exact (mr_blocks_range B MR (aa_laws API) _ _ _ _ _ _ HMR Hin).
rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
apply Hz. exact Hi.
Qed.

End W.

Theorem zlib_calloc_contract_big : calloc_contract_big src0_msyms zlib_API CALLOC_PC.
Proof using.
  exact (calloc_contract_big_ok src0_msyms zlib_API zlib_allocator_extra ltac:(vm_compute; reflexivity) CALLOC_PC
    (@src0_calloc_realizes_big fx rc)).
Qed.

Theorem zlib_calloc_contract_big_cf : calloc_contract_big_cf src0_msyms zlib_API CALLOC_PC.
Proof using.
  exact (calloc_contract_big_cf_ok src0_msyms zlib_API zlib_allocator_extra ltac:(vm_compute; reflexivity) CALLOC_PC
    (@src0_calloc_realizes_big_cf fx rc)).
Qed.

End A.
