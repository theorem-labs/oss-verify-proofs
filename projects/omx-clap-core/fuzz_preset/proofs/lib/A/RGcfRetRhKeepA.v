(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/omx-clap-core/fuzz_preset/lib/A/RGcfSegs3.v (hub dc970db26dad, blob f049bb307485) rw_ret_A, restated over Deallocate's PRIMED raw post (YGcfReallocComposeRh.free_dpost_cf_rh) with the overlay normal form kept (the memnorm proof of RGcfSegs3.v blob a19665e011c3). *)
(* Theorem Labs, 2026-10: fuzz_preset.asan image A: rw_ret_keep_rh_A is the primed S3 WITH the keep, the premise of
   YGcfInstReallocKKeep.wrap_realloc_walk_keep_cf_rh_of (field rwkh_ret of wrap_realloc_walk_keep_cf_rh) at
   segs := tfibsegs, ci := CfImg_A, atpD := 1, ARX := RGcfLaws.ARXqA B, K3 := RGcfSegs2a.K3A B: RGcfRetRhA.rw_ret_rh_A's
   statement and proof with (YAkMemnorm.memnorm segs mem5 -> YAkMemnorm.memnorm segs mem') before errno_kept_cf; the
   machine run RGthinM2.m3 leaves memory unchanged, so the keep is memnorm_pw.
   rule 24: proves no function (kind: segment lemma). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfReallocCompose YP03.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost YGcfReallocComposeRh YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0x AF0m CfImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import RGthinK RGthinM RGthinM2 RGthinS RGcfSegs2a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require RGcfLaws.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.
#[local] Existing Instance CfImg_A.
Lemma memnorm_pw : forall m m' : word -> option byte,
YAkMemnorm.memnorm tfibsegs m -> (forall x, m' x = m x) -> YAkMemnorm.memnorm tfibsegs m'.
Proof. intros m m' M E. apply (YAkMemnorm.memnorm_sub tfibsegs m m' M). intros x b H. rewrite <- (E x). exact H. Qed.

Section b.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Hypothesis LAWSa : forall Hp, RTlaws B (fun inst ly S W mem md => RGcfLaws.ARXqA B Hp inst ly S W mem md) (aowned B).

Local Abbreviation ARXA := (fun (Hp : list Z) (inst : Z) (ly : alayout) (S : astate) (W : world tfibsegs)
  (mem : word -> option byte) (md : Model) => RGcfLaws.ARXqA B Hp inst ly S W mem md).

Theorem rw_ret_keep_rh_A : forall ly S Hp Hp' W regs mem md p n_old n ch q ly2 S2 W4 inst so bp regsD memD mdD ly3 S3 W5 regs5 mem5 md5,
  YGcfReallocCompose.rentry_cf tfibsegs B ly S Hp W regs mem md p n_old n ch ->
  K3A B ly S Hp W regs mem md p n_old n ch q ly2 S2 W4 regsD memD mdD ->
  YGcfReallocCompose.realloc_dpre_cf tfibsegs B 1 ARXA Hp inst so bp ly2 S2 W4 regsD memD mdD p n_old
    (YGcfReallocCompose.rtr_cf ly regs ch) ->
  YGcfReallocComposeRh.free_dpost_cf_rh tfibsegs B ARXA Hp' inst ly2 S2 W4 regsD memD mdD
    (fun a => p <> PNull /\ sptr_addr B ly2 p <= a < sptr_addr B ly2 p + req_size n_old) ly3 S3 W5 regs5 mem5 md5 ->
  qtight S3 ->
  SRr tfibsegs W5 (cfg_at tfibsegs (raZ regsD) regs5 mem5 md5)
  (fun W' c' => exists regs' mem' md',
    c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\
    getr regs' 10 = w64 (sptr_addr B ly2 q) /\
    ARXA Hp' inst ly3 S3 W' mem' md' /\ same_io md5 md' /\
    RGtop.rkeep tfibsegs B regs W5 mem5 W' mem' /\ RGtop.rwin tfibsegs regs W' mem' /\
    (YAkMemnorm.memnorm tfibsegs mem5 -> YAkMemnorm.memnorm tfibsegs mem') /\
    errno_kept_cf B mem5 mem').
Proof using TB LAWSa.
intros ly S Hp Hp' W regs mem md p n_old n ch q ly2 S2 W4 inst so bp regsD memD mdD ly3 S3 W5 regs5 mem5 md5 ENT HK3 DPR DPO LP3.
pose proof (rt_errno B TB) as HERR.
unfold YGcfReallocCompose.rentry_cf, acall_pre_cf in ENT.
destruct ENT as ((ARC0 & Hra & Hsp16 & Hlo & Hbot & Hhi & HWIN & Hgp & Htp & HCH & _) & HBLK & HA0 & HNH & HA1 & HN & HL & HU).
unfold K3A, K3r in HK3. destruct HK3 as (KSP & K1d & K20 & KK & KF & KRR & KW & (Eslo & Eshi & Etop) & QB).
unfold YGcfReallocCompose.realloc_dpre_cf, DeallocG.dealloc_pre in DPR. cbv beta in DPR.
pose proof (proj1 DPR) as ARXD.
pose proof (rt_inst B TB _ _ _ _ _ _ _ ARXD) as EI. subst inst.
assert (DBLK : p = PNull \/ In (p, n_old) (blocks S2)) by (clear - DPR; tauto).
unfold YGcfReallocComposeRh.free_dpost_cf_rh, YGcfRehidePost.dealloc_post_raw_rh, YGcfRehidePost.dealloc_post_rh in DPO.
destruct DPO as ((ARX3 & LLE3 & WLE3 & PRS & SIO & FR5 & PR5) & FR5w).
cbv beta in ARX3.
set (sp0 := spZ regs) in *. set (qa := sptr_addr B ly2 q) in *.
destruct LLE3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop3 & Eslo3 & Eshi3 & _).
pose proof (fun a => rl_stack _ _ _ (LAWSa Hp) ly2 S2 W4 memD mdD a ARXD) as STKD.
pose proof (fun a => rl_stack _ _ _ (LAWSa Hp') ly3 S3 W5 mem5 md5 a ARX3) as STK5.
unfold ASTACK in Hlo, HWIN.
pose proof (proj2 (rl_stack _ _ _ (LAWSa Hp) ly2 S2 W4 memD mdD (ly_stk_lo ly2) ARXD ltac:(rewrite Eslo, Eshi; lia))) as SLO.
rewrite Eslo in SLO.
pose proof (rl_stkhi _ _ _ (LAWSa Hp) ly2 S2 W4 memD mdD ARXD) as SHI. rewrite Eshi in SHI. unfold kHighMemEnd in SHI.
pose proof (proj1 ASAN_CEIL_range) as CR.
assert (PB : forall a, ASAN_CEIL <= a -> ~ (p <> PNull /\ sptr_addr B ly2 p <= a < sptr_addr B ly2 p + req_size n_old)).
{ intros a Ha [Hne Hin]. destruct DBLK as [HP|HP]; [exact (Hne HP)|].
  destruct (rl_blk _ _ _ (LAWSa Hp) ly2 S2 W4 memD mdD p n_old ARXD HP) as (_ & X2 & _). lia. }
(* The re-hidden set lies below the allocator's ceiling, the stack at or above it. *)
assert (DSN : forall a, ASAN_CEIL <= a -> ~ YGcfRehidePost.dead_shadow_new ly2 S2 S3 a).
{ intros a Ha X. pose proof (YGcfRehidePost.dead_shadow_new_below_ceiling ly2 S2 S3 a X) as Y.
  unfold ASAN_CEIL in Ha. lia. }
assert (RAD : raZ regsD = RT_RA_D) by (unfold raZ; rewrite K1d; unfold w64; apply YP03.unsigned_lit_small; unfold RT_RA_D; lia).
assert (STKV : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ (sp0 - 2208 - 8192 <= a < sp0 - 2208) ->
  aview tfibsegs (w_H W5) mem5 a = aview tfibsegs (w_H W4) memD a).
{ intros a Ha Hge. apply FR5.
  - lia.
  - exact (proj1 (STKD a ltac:(rewrite Eslo, Eshi; exact Ha))).
  - exact (proj1 (STK5 a ltac:(rewrite Eslo3, Eshi3, Eslo, Eshi; exact Ha))).
  - unfold ascratch. rewrite HERR. intros [X|X]; [rewrite KSP in X; unfold DFSTACK_G in X; lia | unfold RT_ERRNO in X; lia].
  - apply PB. lia.
  - apply DSN. lia. }
assert (XF : forall a v, ly_stk_lo ly <= a -> a + 8 <= ly_stk_hi ly -> sp0 - 2208 <= a ->
  val_mem tfibsegs (mrestrict (w_H W4) memD) a 8 v -> val_mem tfibsegs (mrestrict (w_H W5) mem5) a 8 v).
{ intros a v H1 H2 H3 V. apply (val_mem_xfer (w_H W4) (w_H W5) memD mem5 a 8 v); [|exact V].
  intros k Hk. apply STKV; lia. }
assert (PW5 : forall a, sp0 - 16384 <= a < sp0 -> apresent (w_H W5) mem5 a).
{ intros a Ha. destruct (Z_le_gt_dec (sp0 - 2208) a) as [L|L]; [|destruct (Z_le_gt_dec (sp0 - 2208 - 8192) a) as [L2|L2]].
  - apply vis_apresent_hi; [unfold TFIB_IMG_END; lia|]. rewrite STKV by lia. apply apresent_vis. apply KW. unfold ASTACK. fold sp0. lia.
  - apply PR5. rewrite KSP. unfold DFSTACK_G. lia.
  - apply vis_apresent_hi; [unfold TFIB_IMG_END; lia|]. rewrite STKV by lia. apply apresent_vis. apply KW. unfold ASTACK. fold sp0. lia. }
destruct KF as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
destruct (win_word (w_H W5) mem5 (sp0 - 2208) ltac:(intros i Hi; apply PW5; lia)) as (w0 & Rw0 & V0).
destruct (win_word (w_H W5) mem5 (sp0 - 2200) ltac:(intros i Hi; apply PW5; lia)) as (w1 & Rw1 & V1).
destruct (win_word (w_H W5) mem5 (sp0 - 2192) ltac:(intros i Hi; apply PW5; lia)) as (w2 & Rw2 & V2).
destruct (win_word (w_H W5) mem5 (sp0 - 2184) ltac:(intros i Hi; apply PW5; lia)) as (w3 & Rw3 & V3).
destruct (win_word (w_H W5) mem5 (sp0 - 2176) ltac:(intros i Hi; apply PW5; lia)) as (w4 & Rw4 & V4).
rewrite RAD. unfold cfg_at at 1.
eapply SRr_mono.
{ apply (m3 W5 md5 regs5 mem5 (sp0 - 2208) qa w0 w1 w2 w3 w4 (raZ regs)
    (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9)) (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19))
    (bv_unsigned (getr regs 20)) (bv_unsigned (getr regs 21)) (bv_unsigned (getr regs 22))).
  - unfold spZ. rewrite (ap_get regsD regs5 2 2%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact KSP.
  - lia.
  - lia.
  - rewrite (ap_get regsD regs5 20 20%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact K20.
  - exact QB.
  - repeat (apply Forall_cons; [first [lia | apply u64_range]|]). apply Forall_nil.
  - unfold rfr_ok. repeat split; try (eapply val_mem_addr; [eassumption | lia]).
    apply XF; [lia | lia | lia | eapply val_mem_addr; [exact KRR | lia]].
  - unfold afr_ok. apply XF; [lia | lia | lia | eapply val_mem_addr; [exact F0 | lia]].
  - unfold ifr_ok. repeat split; (apply XF; [lia | lia | lia | eapply val_mem_addr; [eassumption | lia]]).
  - unfold raZ. rewrite w64_unsigned. exact Hra. }
intros W' c' _ POST. destruct POST as (EW & regs' & mem' & mat & Ec & MEQ & G2 & G1 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G10 & GK).
subst W' c'.
exists regs', mem', (with_vm_backing (m_vm_lazy md5) mat md5).
split; [unfold cfg_at; reflexivity|].
split.
{ apply ap_mk. cs_cases.
  - rewrite G2. assert (E : sp0 - 2208 + 2208 = bv_unsigned (getr regs 2)) by (subst sp0; unfold spZ; lia).
    rewrite E, w64_unsigned. reflexivity.
  - rewrite (GK 3%bv ltac:(cbn; tauto)), (ap_get regsD regs5 3 3%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact (KK 3%bv ltac:(cbn; tauto)).
  - rewrite (GK 4%bv ltac:(cbn; tauto)), (ap_get regsD regs5 4 4%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact (KK 4%bv ltac:(cbn; tauto)).
  - rewrite G8, w64_unsigned. reflexivity.
  - rewrite G9, w64_unsigned. reflexivity.
  - rewrite G18, w64_unsigned. reflexivity.
  - rewrite G19, w64_unsigned. reflexivity.
  - rewrite G20, w64_unsigned. reflexivity.
  - rewrite G21, w64_unsigned. reflexivity.
  - rewrite G22, w64_unsigned. reflexivity.
  - rewrite (GK 23%bv ltac:(cbn; tauto)), (ap_get regsD regs5 23 23%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact (KK 23%bv ltac:(cbn; tauto)).
  - rewrite (GK 24%bv ltac:(cbn; tauto)), (ap_get regsD regs5 24 24%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact (KK 24%bv ltac:(cbn; tauto)).
  - rewrite (GK 25%bv ltac:(cbn; tauto)), (ap_get regsD regs5 25 25%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact (KK 25%bv ltac:(cbn; tauto)).
  - rewrite (GK 26%bv ltac:(cbn; tauto)), (ap_get regsD regs5 26 26%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact (KK 26%bv ltac:(cbn; tauto)).
  - rewrite (GK 27%bv ltac:(cbn; tauto)), (ap_get regsD regs5 27 27%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact (KK 27%bv ltac:(cbn; tauto)). }
split; [exact G10|].
split.
{ cbv beta. apply (rl_write _ _ _ (LAWSa Hp') ly3 S3 W5 mem5 md5 mem' _ ARX3);
    [intros x _ _ _; apply MEQ | intros a _ Hv; rewrite (aview_pw _ mem5 mem' a MEQ); exact Hv | apply sbm_wvb]. }
split; [apply same_io_wvb|].
split; [unfold rkeep; split; [intros a _ _; apply aview_pw; exact MEQ | intros x _; exact (MEQ x)]|].
split.
{ unfold rwin. intros a Ha. fold sp0 in Ha. unfold ASTACK in Ha. apply (apresent_pw _ mem5 mem' a MEQ). apply PW5. lia. }
split; [intros MN; exact (memnorm_pw mem5 mem' MN MEQ)|].
intros i _; apply MEQ.
Qed.
End b.

End a.

Print Assumptions rw_ret_keep_rh_A.
