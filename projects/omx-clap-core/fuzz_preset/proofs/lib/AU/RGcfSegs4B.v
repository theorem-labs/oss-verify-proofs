(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-29: copied from proofs/omx-clap-core/fuzz_preset/lib/A/RGthinS4.v (hub 9f4806388ad, blob ab2a295d7ba3) rt_seg_nret, restated as YGcfReallocCompose.wrap_realloc_walk_cf's field rw_nret at image A (entry facts rentry_cf, errno / oom byte from TfibSyms, memnorm kept). *)
(* Modified by Theorem Labs, 2026-10: relocated from proofs/omx-clap-core/fuzz_preset/lib/A/RGcfSegs4.v (hub 48d2e915d556, blob f0146206a6a3), stated at fuzz_preset's asan image (ELF sha256 bff8519bbe3e), to its asan-ubsan image (ELF sha256 c90d4fa54d43): module paths to the image-B twins, every image numeral by symbol + offset, image bounds by the image-B start-up facts; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import AllocG DeallocG ReallocG RGtop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfMallocCompose.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfReallocCompose YAkMemnorm YP03.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0x YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import RGthinKB RGthinMB RGthinM2B RGthinSB RGcfSegs2aB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require RGcfKB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require RGcfLawsB.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.
#[local] Existing Instance CfImg_B.
Section b.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Hypothesis LAWSa : forall Hp, RTlaws B (fun inst ly S W mem md => RGcfLawsB.ARXqB B Hp inst ly S W mem md) (aowned B).
Hypothesis LAWSm : forall Hp, RTlaws B (fun inst ly S W mem md => RGcfLawsB.ARXqB B Hp inst ly S W mem md) (AOXm_cf B).
Variable nmax : Z.

Local Abbreviation ARXB := (fun (Hp : list Z) (inst : Z) (ly : alayout) (S : astate) (W : world tfibsegs)
  (mem : word -> option byte) (md : Model) => RGcfLawsB.ARXqB B Hp inst ly S W mem md).

Theorem rw_nret_B : forall ly S Hp W regs mem md p n_old n ch S1 W1 inst so bp regsA memA mdA ly2 S2 W2 regs2 mem2 md2,
  YGcfReallocCompose.rentry_cf tfibsegs B ly S Hp W regs mem md p n_old n ch ->
  RGcfKB.K1B B ly S Hp W regs mem md p n_old n ch S1 W1 regsA memA mdA ->
  malloc_apre_cf tfibsegs B nmax 8 1 1 ARXB Hp inst so bp ly S1 W1 regsA memA mdA n (YGcfReallocCompose.rtr_cf ly regs ch) ->
  malloc_apost_cf tfibsegs B ARXB Hp inst ly S1 W1 regsA memA mdA
    (fun a => PNull <> PNull /\ sptr_addr B ly2 PNull <= a < sptr_addr B ly2 PNull + req_size n) ly2 S2 W2 regs2 mem2 md2 ->
  getr regs2 10 = w64 (sptr_addr B ly2 PNull) -> qtight S2 ->
  val_mem tfibsegs (mrestrict (w_H W2) mem2) (as_oom_byte B) 1 1 ->
  In (p, n_old) (blocks S1) -> In (p, n_old) (blocks S2) ->
  SRr tfibsegs W2 (cfg_at tfibsegs (raZ regsA) regs2 mem2 md2)
  (fun W' c' => exists regs' mem' md',
    c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
    ARXB Hp inst ly2 S2 W' mem' md' /\ same_io md2 md' /\
    RGtop.rkeep tfibsegs B regs W2 mem2 W' mem' /\ RGtop.rwin tfibsegs regs W' mem' /\
    (YAkMemnorm.memnorm tfibsegs mem2 -> YAkMemnorm.memnorm tfibsegs mem') /\
    val_mem tfibsegs (mrestrict (w_H W') mem') (as_errno B) 4 12 /\
    val_mem tfibsegs (mrestrict (w_H W') mem') (as_oom_byte B) 1 1).
Proof using TB LAWSa LAWSm.
intros ly S Hp W regs mem md p n_old n ch S1 W1 inst so bp regsA memA mdA ly2 S2 W2 regs2 mem2 md2
  ENT HK1 APR APO A02 LP2 OOM HB1 HB2.
pose proof (rt_errno B TB) as HERR. pose proof (rt_tp B TB) as HTP. pose proof (rt_oom B TB) as HOOM.
rewrite HOOM in OOM |- *.
pose proof (LAWSm Hp) as LAWS.
unfold YGcfReallocCompose.rentry_cf, acall_pre_cf in ENT.
destruct ENT as ((ARC0 & Hra & Hsp16 & Hlo & Hbot & Hhi & HWIN & Hgp & Htp & HCH & _) & HBLK & HA0 & HNH & HA1 & HN & HL & HU).
unfold RGcfKB.K1B, K1r in HK1. destruct HK1 as (KSP & K1ra & K8 & K13 & K9 & K18 & K19 & KK & KF & KRR & KW & KB).
unfold malloc_apre_cf, alloc_pre in APR. pose proof (proj1 APR) as ARX1. cbv beta in ARX1.
pose proof (rt_inst B TB _ _ _ _ _ _ _ ARX1) as EI. subst inst.
unfold malloc_apost_cf, alloc_post in APO. destruct APO as (ARX2 & LLE & WLE & PRS & SIO & FR2 & FR2w & PR2).
cbv beta in ARX2.
set (sp0 := spZ regs) in *.
destruct LLE as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof (fun a => rl_stack _ _ _ LAWS ly S1 W1 memA mdA a ARX1) as STK1.
pose proof (fun a => rl_stack _ _ _ LAWS ly2 S2 W2 mem2 md2 a ARX2) as STK2.
unfold ASTACK in Hlo, HWIN.
pose proof (proj2 (rl_stack _ _ _ LAWS ly S1 W1 memA mdA (ly_stk_lo ly) ARX1 ltac:(lia))) as SLO.
pose proof (rl_stkhi _ _ _ LAWS ly S1 W1 memA mdA ARX1) as SHI. unfold kHighMemEnd in SHI.
pose proof (proj1 ASAN_CEIL_range) as CR.
assert (RAA : raZ regsA = RT_RA_A) by (unfold raZ; rewrite K1ra; unfold w64; apply YP03.unsigned_lit_small; unfold RT_RA_A; lia).
assert (STKV : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ (sp0 - 2208 - 4096 <= a < sp0 - 2208) ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W1) memA a).
{ intros a Ha Hn. apply FR2.
  - lia.
  - exact (proj1 (STK1 a Ha)).
  - exact (proj1 (STK2 a ltac:(rewrite Eslo, Eshi; exact Ha))).
  - unfold ascratch. rewrite HERR. intros [X|X]; [rewrite KSP in X; unfold AFSTACK_G in X; lia | unfold RT_ERRNO in X; lia].
  - intros [X _]. exact (X eq_refl). }
assert (XF : forall a v, ly_stk_lo ly <= a -> a + 8 <= ly_stk_hi ly -> sp0 - 2208 <= a ->
  val_mem tfibsegs (mrestrict (w_H W1) memA) a 8 v -> val_mem tfibsegs (mrestrict (w_H W2) mem2) a 8 v).
{ intros a v H1 H2 H3 V. apply (val_mem_xfer (w_H W1) (w_H W2) memA mem2 a 8 v); [|exact V]. intros k Hk. apply STKV; lia. }
assert (PW2 : forall a, sp0 - 16384 <= a < sp0 -> apresent (w_H W2) mem2 a).
{ intros a Ha. destruct (Z_le_gt_dec (sp0 - 2208) a) as [L|L]; [|destruct (Z_le_gt_dec (sp0 - 2208 - 4096) a) as [L2|L2]].
  - apply vis_apresent_hi; [unfold TFIB_IMG_END; lia|]. rewrite STKV by lia. apply apresent_vis. apply KW. unfold ASTACK. fold sp0. lia.
  - apply PR2. rewrite KSP. unfold AFSTACK_G. lia.
  - apply vis_apresent_hi; [unfold TFIB_IMG_END; lia|]. rewrite STKV by lia. apply apresent_vis. apply KW. unfold ASTACK. fold sp0. lia. }
destruct KF as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
destruct (win_word (w_H W2) mem2 (sp0 - 2208) ltac:(intros i Hi; apply PW2; lia)) as (w0 & Rw0 & V0).
destruct (win_word (w_H W2) mem2 (sp0 - 2200) ltac:(intros i Hi; apply PW2; lia)) as (w1 & Rw1 & V1).
destruct (win_word (w_H W2) mem2 (sp0 - 2192) ltac:(intros i Hi; apply PW2; lia)) as (w2 & Rw2 & V2).
destruct (win_word (w_H W2) mem2 (sp0 - 2184) ltac:(intros i Hi; apply PW2; lia)) as (w3 & Rw3 & V3).
destruct (win_word (w_H W2) mem2 (sp0 - 2176) ltac:(intros i Hi; apply PW2; lia)) as (w4 & Rw4 & V4).
rewrite RAA. unfold cfg_at at 1.
eapply SRr_mono.
{ apply (m4 W2 md2 regs2 mem2 (sp0 - 2208) w0 w1 w2 w3 w4 (raZ regs)
    (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9)) (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19))
    (bv_unsigned (getr regs 20)) (bv_unsigned (getr regs 21)) (bv_unsigned (getr regs 22))).
  - unfold spZ. rewrite (ap_get regsA regs2 2 2%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact KSP.
  - lia.
  - lia.
  - rewrite A02. cbn [sptr_addr sptr_exp aeval]. reflexivity.
  - rewrite (ap_get regsA regs2 4 4%bv PRS ltac:(unfold acallee_saved; lia) eq_refl), (KK 4%bv ltac:(cbn; tauto)), Htp, HTP. reflexivity.
  - repeat (apply Forall_cons; [first [lia | apply u64_range]|]). apply Forall_nil.
  - unfold rfr_ok. repeat split; try (eapply val_mem_addr; [eassumption | lia]).
    apply XF; [lia | lia | lia | eapply val_mem_addr; [exact KRR | lia]].
  - unfold afr_ok. apply XF; [lia | lia | lia | eapply val_mem_addr; [exact F0 | lia]].
  - unfold ifr_ok. repeat split; (apply XF; [lia | lia | lia | eapply val_mem_addr; [eassumption | lia]]).
  - intros a Ha. apply PW2. lia.
  - unfold raZ. rewrite w64_unsigned. exact Hra. }
intros W' c' _ POST. destruct POST as (EW & regs' & mem' & mat & Ec & (MR1 & MR2 & MR3 & MR4) & G2 & G1 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G10 & GK).
subst W' c'.
exists regs', mem', (with_vm_backing (m_vm_lazy md2) mat md2).
split; [unfold cfg_at; reflexivity|].
split.
{ apply ap_mk. cs_cases.
  - rewrite G2. assert (E : sp0 - 2208 + 2208 = bv_unsigned (getr regs 2)) by (subst sp0; unfold spZ; lia).
    rewrite E, w64_unsigned. reflexivity.
  - rewrite (GK 3%bv ltac:(cbn; tauto)), (ap_get regsA regs2 3 3%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact (KK 3%bv ltac:(cbn; tauto)).
  - rewrite (GK 4%bv ltac:(cbn; tauto)), (ap_get regsA regs2 4 4%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact (KK 4%bv ltac:(cbn; tauto)).
  - rewrite G8, w64_unsigned. reflexivity.
  - rewrite G9, w64_unsigned. reflexivity.
  - rewrite G18, w64_unsigned. reflexivity.
  - rewrite G19, w64_unsigned. reflexivity.
  - rewrite G20, w64_unsigned. reflexivity.
  - rewrite G21, w64_unsigned. reflexivity.
  - rewrite G22, w64_unsigned. reflexivity.
  - rewrite (GK 23%bv ltac:(cbn; tauto)), (ap_get regsA regs2 23 23%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact (KK 23%bv ltac:(cbn; tauto)).
  - rewrite (GK 24%bv ltac:(cbn; tauto)), (ap_get regsA regs2 24 24%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact (KK 24%bv ltac:(cbn; tauto)).
  - rewrite (GK 25%bv ltac:(cbn; tauto)), (ap_get regsA regs2 25 25%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact (KK 25%bv ltac:(cbn; tauto)).
  - rewrite (GK 26%bv ltac:(cbn; tauto)), (ap_get regsA regs2 26 26%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact (KK 26%bv ltac:(cbn; tauto)).
  - rewrite (GK 27%bv ltac:(cbn; tauto)), (ap_get regsA regs2 27 27%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact (KK 27%bv ltac:(cbn; tauto)). }
split; [exact G10|].
split.
{ cbv beta. apply (rl_write _ _ _ LAWS ly2 S2 W2 mem2 md2 mem' _ ARX2).
  - intros x Hst Her _. apply MR1; [|exact Her]. rewrite Eslo, Eshi in Hst. intros Hin. apply Hst. lia.
  - intros a Ha Hv. exact (MR4 a Ha Hv).
  - apply sbm_wvb. }
split; [apply same_io_wvb|].
split.
{ unfold rkeep. split.
  - intros a Ha Hs. apply aview_same. apply MR1.
    + intros Hin. apply Hs. unfold ascratch. left. fold sp0. unfold ASTACK.
      rewrite YP03.unsigned_lit_small in Hin by lia. lia.
    + intros Hin. apply Hs. unfold ascratch. right. rewrite HERR.
      rewrite YP03.unsigned_lit_small in Hin by lia. lia.
  - intros x Hs. apply MR1.
    + intros Hin. apply Hs. unfold ascratch. left. fold sp0. unfold ASTACK. lia.
    + intros Hin. apply Hs. unfold ascratch. right. rewrite HERR. lia. }
split.
{ unfold rwin. intros a Ha. fold sp0 in Ha. unfold ASTACK in Ha.
  destruct (Z_le_gt_dec (sp0 - 2176) a) as [L|L]; [destruct (Z_lt_ge_dec a (sp0 - 2160)) as [L2|L2]|].
  - apply MR3. lia.
  - apply (apresent_same (w_H W2) mem2 mem' a); [apply MR1; [rewrite YP03.unsigned_lit_small by lia; lia
      | rewrite YP03.unsigned_lit_small by lia; unfold RT_ERRNO; lia] | apply PW2; lia].
  - apply (apresent_same (w_H W2) mem2 mem' a); [apply MR1; [rewrite YP03.unsigned_lit_small by lia; lia
      | rewrite YP03.unsigned_lit_small by lia; unfold RT_ERRNO; lia] | apply PW2; lia]. }
split; [intros MN; apply (memnorm_se mem2 mem' (sp0 - 2208 + 32) (sp0 - 2208 + 48) MN MR1); [lia | lia]|].
split; [rewrite HERR; exact MR2|].
apply (val_mem_raw (w_H W2) mem2 mem' RT_OOM 1 1); [|exact OOM].
intros k Hk. apply MR1; rewrite YP03.unsigned_lit_small by (unfold RT_OOM; lia); unfold RT_OOM, RT_ERRNO in *; lia.
Qed.
End b.
End a.
