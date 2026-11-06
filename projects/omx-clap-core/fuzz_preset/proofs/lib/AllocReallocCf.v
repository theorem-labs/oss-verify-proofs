(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YN03.v, with its module paths and module names changed; 426 of its 462 lines of code are new or changed and 500 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/AllocCut.v, with its module paths changed; 151 of its 201 lines of code are new or changed and 412 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YK15 YM06 YM06_cf YM05 YM02 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YO0i YO0f YO0g YO0q YO0x YO0d YO0e YO05 YO02 YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO16 YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO10 YO0s YO0u YO15 YN03 YN2b YN33.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0d_cf YO03_cf YO0n_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import AllocSI AllocGS AllocFree AllocMalloc AllocRealloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import AllocMB AllocMallocPath AllocFreePath AllocReallocOK.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract AllocSlots AllocCut AllocForm SlotAgree AllocCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import AllocPack AllocPackRoom AllocPackCut.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import AllocPackGSF AllocPackGSFm AllocPackGSFr AllocPackCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import AllocReallocRoom AllocUnif.
Import ListNotations.
Local Open Scope Z_scope.

Section A. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Section W.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Lemma realloc_post_of_leaf : AllocExtra B MR -> ro_apart_b B = true ->
  forall L A regs mem md p k n old tr q A' c' (P : astate -> Prop),
  call_pre_k B MR REALLOC_STACK L A regs mem md -> ro_agree segs mem -> In (p, k) (user_blocks A) ->
  0 <= n ->
  (forall i, 0 <= i < k -> mbyte segs mem (ptr_addr L p + i) = nth_error old (Z.to_nat i)) ->
  cpath04 (realloc (Some p) n A) tr (Some q, A') ->
  realloc_leaf B MR L A regs mem md p k n (Some q, A') c' -> P A' ->
  realloc_post_cf B API L A regs mem md p k n old P c'.
Proof using.
intros AX HB L A regs mem md p k n old tr q A' c' P Hpre Hro Hin Hn0 Hold Hp HL HP.
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
pose proof Hpre as (HMR0 & _ & _ & _ & _ & Hsp & _).
destruct HL as (L' & regs' & mem' & md' & -> & Hpost & HM). cbn [fst snd] in *.
destruct HM as (Ha0 & Hnz & (l1 & l2 & m1 & m2 & E1 & E3 & E2) & Hcp).
assert (Hin' : In (q, n) (user_blocks A')) by (rewrite E2; apply in_app_iff; right; left; reflexivity).
assert (Hsub : forall q0 k0, In (q0, k0) (user_blocks A) -> q0 <> p -> In (q0, k0) (user_blocks A')).
{ intros q0 k0 Hq Hne. rewrite E1 in Hq. rewrite E2.
  assert (H12 : In (q0, k0) (l1 ++ l2)).
  { apply in_app_iff in Hq as [Hq|[Hq|Hq]]; apply in_app_iff;
    [left; exact Hq | injection Hq as -> _; exfalso; exact (Hne eq_refl) | right; exact Hq]. }
  rewrite <- E3 in H12. apply in_app_iff in H12 as [H12|H12]; apply in_app_iff; [left; exact H12 | right; right; exact H12]. }
pose proof Hpost as (HMR & HW' & _ & _ & Hstab & _ & _ & _ & Hkeep & _).
exists L', A', regs', mem', md', (ptr_addr L' q).
split; [reflexivity|]. split; [exact Hpost|]. split; [exact Ha0|]. split; [exact Hnz|].
split; [exact (mr_blocks_aligned B MR (aa_laws API) _ _ _ _ _ _ HMR Hin')|].
split.
{ destruct (mr_blocks_range B MR (aa_laws API) _ _ _ _ _ _ HMR Hin') as [R1 R2].
split; [exact R1|]. split; [exact R2|]. intros i Hi. exact (ax_blocks_img AX _ _ _ _ _ _ i HMR Hin' Hi). }
split; [exact (blocks_repl L L' A A' p k q n l1 l2 m1 m2 Hstab E1 E3 E2)|].
split.
{ apply (kept_of_post B L A A' mem mem'); [exact Hkeep|]. intros q0 k0 Hq Hg. apply Hsub; [exact Hq|]. intros ->. exact (Hg eq_refl). }
split; [exact (ro_agree_post B MR REALLOC_STACK L A regs mem md _ L' A' regs' mem' md' AX HB Hsp HMR0
(fun a Ha => ex_intro _ p (ex_intro _ k (conj Hin Ha))) Hpost Hro)|].
split; [exact (guard_kept_post B MR L A mem md L' A' mem' md' AX HMR0 HMR)|].
split; [exact Hsub|].
split; [intros i Hi; rewrite Hcp by lia; apply Hold; lia|].
split; [exact (YI04.init_done_of_block A' (q, n) HW' Hin')|].
split; [exact (regions_grow_realloc A p k n tr (Some q) A' HW Hin Hn0 Hp)|].
exact HP.
Qed.

Lemma malloc_ret_of_null_leaf : AllocExtra B MR -> ro_apart_b B = true ->
  forall L A regs mem md n tr q A' c' (P : astate -> Prop),
  call_pre_k B MR REALLOC_STACK L A regs mem md -> ro_agree segs mem -> 0 <= n ->
  cpath04 (malloc n A) tr (Some q, A') ->
  realloc_null_leaf B MR L A regs mem md n (Some q, A') c' -> P A' ->
  exists L' regs' mem' md' res,
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    call_post_k B MR REALLOC_STACK L A regs mem md (fun _ => False) L' A' regs' mem' md' /\
    getr regs' 10 = Z_to_bv 64 res /\ res <> 0 /\ res mod 16 = 0 /\ fresh_block B res n /\
    (exists b1 b2, blocks L' A' = b1 ++ (res, n) :: b2 /\ blocks L A = b1 ++ b2) /\
    blocks_kept B L A mem mem' (fun _ => False) /\
    ro_agree segs mem' /\ guard_kept B mem mem' /\
    (forall p k, In (p, k) (user_blocks A) -> In (p, k) (user_blocks A')) /\
    st_init_done A' = true /\
    (length (st_regions A) <= length (st_regions A'))%nat /\ P A'.
Proof using.
intros AX HB L A regs mem md n tr q A' c' P Hpre Hro Hn0 Hp HL HP.
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
pose proof Hpre as (HMR0 & _ & _ & _ & _ & Hsp & _).
destruct HL as (L' & regs' & mem' & md' & -> & Hpost & Ha0 & Hnz & (l1 & l2 & E1 & E2)). cbn [fst snd] in *.
assert (Hin : In (q, n) (user_blocks A')) by (rewrite E1; apply in_app_iff; right; left; reflexivity).
assert (Hsub : forall p k, In (p, k) (user_blocks A) -> In (p, k) (user_blocks A')).
{ intros p k Hq. rewrite E2 in Hq. rewrite E1. apply in_app_iff in Hq as [Hq|Hq]; apply in_app_iff;
[left; exact Hq | right; right; exact Hq]. }
pose proof Hpost as (HMR & HW' & _ & _ & Hstab & _ & _ & _ & Hkeep & _).
exists L', regs', mem', md', (ptr_addr L' q).
split; [reflexivity|]. split; [exact Hpost|]. split; [exact Ha0|]. split; [exact Hnz|].
split; [exact (mr_blocks_aligned B MR (aa_laws API) _ _ _ _ _ _ HMR Hin)|].
split.
{ destruct (mr_blocks_range B MR (aa_laws API) _ _ _ _ _ _ HMR Hin) as [R1 R2].
split; [exact R1|]. split; [exact R2|]. intros i Hi. exact (ax_blocks_img AX _ _ _ _ _ _ i HMR Hin Hi). }
split; [exact (blocks_add L L' A A' q n l1 l2 Hstab E1 E2)|].
split; [apply (kept_of_post B L A A' mem mem'); [exact Hkeep | intros p k Hq _; exact (Hsub p k Hq)]|].
split; [exact (ro_agree_post B MR REALLOC_STACK L A regs mem md _ L' A' regs' mem' md' AX HB Hsp HMR0
(fun a (F0 : False) => match F0 with end) Hpost Hro)|].
split; [exact (guard_kept_post B MR L A mem md L' A' mem' md' AX HMR0 HMR)|].
split; [exact Hsub|].
split; [exact (YI04.init_done_of_block A' (q, n) HW' Hin)|].
split; [exact (regions_grow_malloc A n tr (Some q) A' HW Hn0 Hp)|].
exact HP.
Qed.

Theorem realloc_contract_cf_ok : AllocExtra B MR -> ro_apart_b B = true -> realloc_realizes_cf B MR -> realloc_safe_p ->
  forall pc, ms_realloc B = Some pc -> realloc_contract_cf B API pc.
Proof using.
intros AX HB HRr HS pc Hpc L A regs mem md p k n old b Hpre Hro Hin H10 H11 Hold Hlen HR HRc T HK.
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
pose proof HRc as [HRm _].
pose proof (room_slots_n b n HRm) as [Hn Ov].
assert (Hroom : roomcf (vm_limit (m_vmmaps md)) (realloc (Some p) n A)).
{ apply (roomcf_realloc A p k n _ HW Hin (proj1 HR) Hn (slots_room4 A b n HW HR HRm) (room_slots_req b n HRm)).
  exact (room_cf_peak A b n md HW HR HRc). }
refine (mreal_cf_SRcf B (realloc (Some p) n A) _ _ (HRr pc L A regs mem md p k n Hpc Hpre Hin H10 H11 Hn)
  (HS A p k n HW Hin Hn) (sb_realloc_ok04 A b p k n HW Hin HR HRm) Hroom T _).
intros c' Hc'. apply HK. clear HK T.
destruct Hc' as ([r A'] & tr & Hp & HL).
destruct (sb_realloc A b p k n tr r A' HW Hin HR HRm Hp) as [[q ->] HRA'].
exact (realloc_post_of_leaf AX HB L A regs mem md p k n old tr q A' c' _ Hpre Hro Hin (proj1 Hn) Hold Hp HL HRA').
Qed.

Theorem realloc_null_contract_cf_ok : AllocExtra B MR -> ro_apart_b B = true -> realloc_null_realizes_cf B MR ->
  forall pc, ms_realloc B = Some pc -> realloc_null_contract_cf B API pc.
Proof using.
intros AX HB HRz pc Hpc L A regs mem md n b Hpre Hro H10 H11 Hra HR HRc T HK.
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
pose proof HRc as [HRm _].
pose proof (room_slots_n b n HRm) as [Hn Ov].
assert (Hroom : roomcf (vm_limit (m_vmmaps md)) (realloc None n A)).
{ apply (roomcf_realloc_null A n _ HW (proj1 HR) Hn (slots_room4 A b n HW HR HRm)).
  exact (room_cf_peak A b n md HW HR HRc). }
refine (mreal_cf_SRcf B (realloc None n A) _ _ (HRz pc L A regs mem md n Hpc Hpre H10 H11 Hn Hra)
  (malloc_safe A n HW ltac:(lia)) (malloc_slots_ok04 A b n HW HR HRm) Hroom T _).
intros c' Hc'. apply HK. clear HK T.
destruct Hc' as ([r A'] & tr & Hp & HL).
change (realloc None n A) with (malloc n A) in Hp.
destruct (malloc_slots_step A b n tr r A' HW HR HRm Hp) as [[q ->] HRA'].
destruct (malloc_ret_of_null_leaf AX HB L A regs mem md n tr q A' c' (fun A1 => res_ok_slots A1 (sb_malloc b n)) Hpre Hro (proj1 Hn) Hp HL HRA')
  as (L' & regs' & mem' & md' & res & Hall).
unfold malloc_ret. exists L', A', regs', mem', md', res. exact Hall.
Qed.

(* The pack form: rf_ok pack_cf_form = res_ok_pack /\ GSF, room room_cf_pack. *)
Definition pack_realloc_contract_cf (pc : Z) : Prop :=
  forall L A regs mem md p k n old b,
    call_pre_k B MR REALLOC_STACK L A regs mem md -> ro_agree segs mem -> In (p, k) (user_blocks A) ->
    getr regs 10 = Z_to_bv 64 (ptr_addr L p) -> getr regs 11 = Z_to_bv 64 n ->
    (forall i, 0 <= i < k -> mbyte segs mem (ptr_addr L p + i) = nth_error old (Z.to_nat i)) ->
    Z.of_nat (length old) = k ->
    rf_ok pack_cf_form A b -> room_cf_pack md b n ->
    SRcf B (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
      (realloc_post_cf B API L A regs mem md p k n old (fun A' => rf_ok pack_cf_form A' (rf_realloc pack_cf_form b k n))).

Definition pack_realloc_null_contract_cf (pc : Z) : Prop :=
  forall L A regs mem md n b,
    call_pre_k B MR REALLOC_STACK L A regs mem md -> ro_agree segs mem ->
    getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 n -> getr regs 1 <> Z_to_bv 64 (ms_malloc B) ->
    rf_ok pack_cf_form A b -> room_cf_pack md b n ->
    SRcf B (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
      (malloc_ret_r B API pack_cf_form REALLOC_STACK L A regs mem md n b).

Theorem pack_realloc_contract_cf_ok : AllocExtra B MR -> ro_apart_b B = true -> realloc_realizes_cf B MR ->
  realloc_safe_p -> forall pc, ms_realloc B = Some pc -> pack_realloc_contract_cf pc.
Proof using.
intros AX HB HRr HS pc Hpc L A regs mem md p k n old b Hpre Hro Hin H10 H11 Hold Hlen [HR HG] HRc T HK.
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
pose proof HRc as [HRm _].
pose proof (room_pack_n b n HRm) as [Hn Ov].
assert (Hroom : roomcf (vm_limit (m_vmmaps md)) (realloc (Some p) n A)).
{ apply (roomcf_realloc A p k n _ HW Hin (proj1 HR) Hn (pack_room4 A b n HW HR HRm) (room_pack_req b n HRm)).
  exact (room_cf_pack_peak A b n md HW HR HG HRc). }
refine (mreal_cf_SRcf B (realloc (Some p) n A) _ _ (HRr pc L A regs mem md p k n Hpc Hpre Hin H10 H11 Hn)
  (HS A p k n HW Hin Hn) (fl_realloc_ok04 pack_form pack_laws A b p k n HW Hin HR HRm) Hroom T _).
intros c' Hc'. apply HK. clear HK T.
destruct Hc' as ([r A'] & tr & Hp & HL).
destruct (realloc_pack_step A b p k n tr r A' HW Hin HR HRm Hp) as [[q ->] HRA'].
pose proof (realloc_GSF A p k n tr (Some q) A' HW Hin HG (proj1 Hn) (cpath04_yields _ _ _ Hp)) as HG'.
exact (realloc_post_of_leaf AX HB L A regs mem md p k n old tr q A' c' _ Hpre Hro Hin (proj1 Hn) Hold Hp HL (conj HRA' HG')).
Qed.

Theorem pack_realloc_null_contract_cf_ok : AllocExtra B MR -> ro_apart_b B = true -> realloc_null_realizes_cf B MR ->
  forall pc, ms_realloc B = Some pc -> pack_realloc_null_contract_cf pc.
Proof using.
intros AX HB HRz pc Hpc L A regs mem md n b Hpre Hro H10 H11 Hra [HR HG] HRc T HK.
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
pose proof HRc as [HRm _].
pose proof (room_pack_n b n HRm) as [Hn Ov].
assert (Hn0 : 0 <= n) by lia.
pose proof (pack_room4 A b n HW HR HRm) as R4.
assert (Hroom : roomcf (vm_limit (m_vmmaps md)) (realloc None n A)).
{ apply (roomcf_realloc_null A n _ HW (proj1 HR) Hn R4).
  exact (room_cf_pack_peak A b n md HW HR HG HRc). }
pose proof (OK4_malloc n A (malloc_reqs_ok A n HW Hn0) (proj1 HR) Hn0 R4) as [HOK _].
refine (mreal_cf_SRcf B (realloc None n A) _ _ (HRz pc L A regs mem md n Hpc Hpre H10 H11 Hn Hra)
  (malloc_safe A n HW Hn0) HOK Hroom T _).
intros c' Hc'. apply HK. clear HK T.
destruct Hc' as ([r A'] & tr & Hp & HL).
change (realloc None n A) with (malloc n A) in Hp.
destruct (malloc_pack_step A b n tr r A' HW HR HRm Hp) as [[q ->] HRA'].
pose proof (malloc_GSF A n tr (Some q) A' HW HG Hn0 (cpath04_yields _ _ _ Hp)) as HG'.
destruct (malloc_ret_of_null_leaf AX HB L A regs mem md n tr q A' c' (fun A1 => rf_ok pack_cf_form A1 (rf_malloc pack_cf_form b n)) Hpre Hro Hn0 Hp HL (conj HRA' HG'))
  as (L' & regs' & mem' & md' & res & Hall).
unfold malloc_ret_r. exists L', A', regs', mem', md', res. exact Hall.
Qed.

End W.
End A.
