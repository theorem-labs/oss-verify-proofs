(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YN03.v, with its module paths and module names changed; 425 of its 462 lines of code are new or changed and 499 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/AllocCut.v, with its module paths and module names changed; 70 of its 141 lines of code are new or changed and 391 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YK11 YK0s YK0i YK15 YM06 YM06_cf YM05 YM02 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import
YO0i YO0f YO0g YO0q YO0x YO0d YO0e YO05 YO02 YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO16 YL01.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YO10 YO0s YO0u YO15 YN03 YN2b YN33.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YO0d_cf YO03_cf YO0n_cf YH02 YN09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require YI04 YN0e_cf YN0i_cf YN10_cf YN23_cf YN0x_cf.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import PlaceCap.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U Require Import AllocSI AllocGS AllocCount AllocBound AllocDepth AllocFree AllocMalloc AllocRealloc.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U Require Import AllocMB AllocMallocMB AllocFreeMB AllocReallocMB AllocMallocPath AllocFreePath.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U Require Import Contract AllocSlots AllocCut SlotAgree ZAllocator.
Import ListNotations.
Local Open Scope Z_scope.

Section A. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Theorem src0_free_null_cf : free_null_contract_cf src0_msyms.
Proof using.
  intros regs mem md Hret H10 Hh Hlz T HK.
  apply (SR_cf_crealizes (ms_segs src0_msyms) _
    (fun c' => c' = mkCfg (mkst regs (getr regs 1) mem (seg_rom (ms_segs src0_msyms))) md) T); [|exact HK].
  eapply SR_cf_msteps; [exact Hh | exact Hlz | apply (src0_free_null_msteps regs mem _ H10) |].
  apply SR_cf_ret. unfold YK0s.ret_ok in Hret. rewrite Hret. reflexivity.
Qed.

Theorem src0_malloc_realizes_cf : malloc_realizes_cf src0_msyms (MRx src0_msyms).
Proof using.
  exact (YN0e_cf.src0_malloc_realizes YN0i_cf.src0_alloc_meta (YN23_cf.src0_malloc_small YN10_cf.src0_alloc_slot)).
Qed.

Theorem src0_free_realizes_cf : free_realizes_cf src0_msyms (MRx src0_msyms).
Proof using. exact YN0x_cf.src0_free_realizes_closed. Qed.

Lemma room_cf_peak : forall A b n md, WF A -> res_ok_slots A b -> room_cf md b n ->
  LIVE_UB A + 3 * PGSZ + area A + Z.max MMAX (page_round (n + IB + UNIT)) <= vm_limit (m_vmmaps md).
Proof using.
  intros A b n md HW (HII & HSI & HGS & HNL & HNR & (MB1 & MB2) & Hnb & Hub & Hlv & Hby & Hh)
    [(Hn & Hcap & C1 & C2 & C3 & C4) Hlim].
  pose proof (map_count_bound A HW HSI) as T4.
  pose proof (map_bytes_bound A HW HSI HGS) as T7.
  pose proof (nareas_hand A HII) as NA1.
  destruct (shift_small A (HCAP (sb_cap b)) HII Hh C4) as [SH1 SH2].
  pose proof HII as (_ & Hsh & _ & _ & Hrt & _).
  assert (HD : hand A / METAS_PER_AREA <= HCAP (sb_cap b) / METAS_PER_AREA).
  { apply Z.div_le_mono; [unfold METAS_PER_AREA; lia | exact Hh]. }
  assert (BK : brk_bytes A / PGSZ <= nareas A + 1).
  { apply Z.div_le_upper_bound; [unfold PGSZ; lia|]. unfold PGSZ in *. lia. }
  pose proof (page_round_ge (n + IB + UNIT)) as PR. pose proof (page_round_lt (n + IB + UNIT)) as PR'.
  assert (MX0 : 0 < MMAX) by (unfold MMAX; reflexivity).
  assert (AR : area A <= AREA_BOUND (sb_cap b)) by (unfold area, AREA_BOUND, P2; unfold PGSZ in *; lia).
  assert (RQ1 : AREA_BOUND (sb_cap b) <= RQ_BOUND (sb_cap b) n) by (unfold RQ_BOUND; lia).
  unfold NONHEAP_CF in Hlim. unfold MG_REQ in C3.
  unfold LIVE_UB. rewrite Hrt. unfold LIVE_BOUND, AREA_BOUND, NA, P2, RQ_BOUND in *. unfold PGSZ, MMAX, IB, UNIT in *. lia.
Qed.

Section W.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Theorem malloc_contract_cf_ok : AllocExtra B MR -> ro_apart_b B = true -> malloc_realizes_cf B MR ->
  malloc_contract_cf B API.
Proof using.
intros AX HB HMcf L A regs mem md n b Hpre Hro Hn HR HRc T HK.
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
pose proof HRc as [HRm _].
pose proof (room_slots_n b n HRm) as [Hn62 _].
assert (Hn0 : 0 <= n) by lia.
assert (Hroom : roomcf (vm_limit (m_vmmaps md)) (malloc n A)).
{ apply roomcf_malloc; [apply malloc_reqs_ok; [exact HW | exact Hn0] | exact (proj1 HR) | exact Hn0 |
    exact (slots_room4 A b n HW HR HRm) | exact (room_cf_peak A b n md HW HR HRc)]. }
pose proof (mreal_cf_SR_cfv segs (malloc n A) _ _ (HMcf L A regs mem md n Hpre Hn Hn62)
  (malloc_safe A n HW Hn0) (malloc_slots_ok04 A b n HW HR HRm) Hroom) as HS.
apply (SR_cfv_crealizes segs _ _ T HS). intros c' Hc'. apply HK. clear HS HK T.
destruct Hc' as ([r A'] & tr & Hp & HL).
destruct (malloc_slots_step A b n tr r A' HW HR HRm Hp) as [[p ->] HRA'].
destruct HL as (L' & regs' & mem' & md' & -> & Hpost & Ha0 & Hnz & (l1 & l2 & E1 & E2) & _).
pose proof Hpre as (HMR0 & _ & _ & _ & _ & Hsp & _).
cbn [fst snd] in *.
assert (Hin : In (p, n) (user_blocks A')) by (rewrite E1; apply in_app_iff; right; left; reflexivity).
assert (Hsub : forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')).
{ intros q k Hq. rewrite E2 in Hq. rewrite E1. apply in_app_iff in Hq as [Hq|Hq]; apply in_app_iff;
[left; exact Hq | right; right; exact Hq]. }
pose proof Hpost as (HMR & HW' & _ & _ & Hstab & _ & _ & _ & Hkeep & _).
pose proof (proj1 (call_post_k_alloc B MR L A regs mem md _ L' A' regs' mem' md') Hpost) as Hpk.
unfold malloc_ret. exists L', A', regs', mem', md', (ptr_addr L' p).
split; [reflexivity|].
split; [exact Hpk|].
split; [exact Ha0|]. split; [exact Hnz|].
split; [exact (mr_blocks_aligned B MR (aa_laws API) _ _ _ _ _ _ HMR Hin)|].
split.
{ destruct (mr_blocks_range B MR (aa_laws API) _ _ _ _ _ _ HMR Hin) as [R1 R2].
split; [exact R1|]. split; [exact R2|]. intros i Hi. exact (ax_blocks_img AX _ _ _ _ _ _ i HMR Hin Hi). }
split; [exact (blocks_add L L' A A' p n l1 l2 Hstab E1 E2)|].
split; [apply (kept_of_post B L A A' mem mem'); [exact Hkeep | intros q k Hq _; exact (Hsub q k Hq)]|].
split; [exact (ro_agree_post B MR ALLOC_STACK L A regs mem md _ L' A' regs' mem' md' AX HB Hsp HMR0
(fun a (F : False) => match F with end) Hpk Hro)|].
split; [exact (guard_kept_post B MR L A mem md L' A' mem' md' AX HMR0 HMR)|].
split; [exact Hsub|].
split; [exact (YI04.init_done_of_block A' (p, n) HW' Hin)|].
split; [exact (regions_grow_malloc A n tr (Some p) A' HW Hn0 Hp)|].
exact HRA'.
Qed.

Theorem free_contract_cf_ok : AllocExtra B MR -> ro_apart_b B = true -> free_realizes_cf B MR ->
  free_contract_cf B API.
Proof using.
intros AX HB HFcf L A regs mem md p n b Hpre Hro Hin Hp HR T HK.
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
pose proof (free_reqs_ok A p n HW Hin) as RQ.
pose proof (OK4_free (Some p) A RQ (proj1 HR)) as [HOK _].
pose proof (mreal_cf_SR_cfv segs (free (Some p) A) _ _ (HFcf L A regs mem md p n Hpre Hin Hp)
  (free_safe A p n HW Hin) HOK (r_free (Some p) (vml (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom segs)) md)) A)) as HS.
apply (SR_cfv_crealizes segs _ _ T HS). intros c' Hc'. apply HK. clear HS HK T.
destruct Hc' as ([[] A'] & tr & Hcp & HL).
pose proof (free_slots_step A b p n tr tt A' HW Hin HR Hcp) as HRA'.
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
exact HRA'.
Qed.

End W.

Theorem zlib_malloc_contract_cf : malloc_contract_cf src0_msyms zlib_API.
Proof using.
  exact (malloc_contract_cf_ok src0_msyms zlib_API zlib_allocator_extra ltac:(vm_compute; reflexivity) src0_malloc_realizes_cf).
Qed.

Theorem zlib_free_contract_cf : free_contract_cf src0_msyms zlib_API.
Proof using.
  exact (free_contract_cf_ok src0_msyms zlib_API zlib_allocator_extra ltac:(vm_compute; reflexivity) src0_free_realizes_cf).
Qed.

End A.
