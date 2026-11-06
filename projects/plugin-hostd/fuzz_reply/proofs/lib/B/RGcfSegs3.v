(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-29: copied from proofs/omx-clap-core/fuzz_preset/lib/A/RGthinS3.v (hub 9f4806388ad, sha256 7fa7473b008e; internal record) rt_seg_ret, restated as YGcfReallocCompose.wrap_realloc_walk_cf's field rw_ret at image A (entry facts rentry_cf, Deallocate's post at any ghost set, errno / memnorm kept). *)
(* Modified by Theorem Labs, 2026-10-31: field round 3 part 3c (the record's segments no longer keep the overlay normal
   form): rw_ret_A's memnorm conjunct and its proof removed. *)
(* Modified by Theorem Labs, 2026-10-31: relocated from fuzz_preset (commit dc970db26dad) to fuzz_reply's asan image A (unstripped fuzz_reply.asan sha256 d751b179ea49, pin 42c58610e125): module paths changed (AllocG DeallocG RGtop YGcfMallocCompose YGcfReallocCompose from lib.Reusable to lib.A) and no image numeral in it. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/RGcfSegs3.v at commit 6ea216c338f as lib/B/RGcfSegs3.v, with its module paths changed (lib.A to lib.B, except the image-free ADIfaceImgA and the one params file CfParamsReply; the image twins A<r> to Y<r>, CfImgA / CfImg_A to CfImgB / CfImg_B, WrapAKit / WrapFreeA<x> to WrapBKit / WrapFreeB<x>, AFf0cfR to YFf0cfR, RGcfWalkA to RGcfWalkB with its three exported names wrap_realloc_walk_cf_A, wrap_realloc_null_walk_cf_A, wrap_realloc_walk_cf_rh_A to _B), and no numeral of it names an image address that differs in fuzz_reply.asan-ubsan. *)
(* Theorem Labs, 2026-10: fuzz_preset.asan image A, row A5: the segment S3, Deallocate's return
   into Reallocate -> realloc's return with a0 = the new block: YGcfReallocCompose.wrap_realloc_walk_cf's field rw_ret
   at segs := tfibsegs, ci := CfImg_A, atpD := 1, ARX := RGcfLaws.ARXqA B, K3 := K3A B (A/RGcfSegs2a.v),
   with Deallocate's post at ANY ghost set Hp', under the allocator law LAWSa (A/RGcfLaws.v rt_laws_aowned, at Hp for
   Deallocate's pre and at Hp' for its post). The proof is RGthinS3.rt_seg_ret's over the machine run RGthinM2.m3,
   with the entry facts of rentry_cf (the stack bounds from Deallocate's pre on the same stack) and errno kept (m3
   leaves memory unchanged). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AllocG DeallocG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ReallocG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import RGtop.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfMallocCompose.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfReallocCompose.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YP03.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YF0x YF0m CfImgB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import RGthinK RGthinM RGthinM2 RGthinS RGcfSegs2a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require RGcfLaws.
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
Hypothesis LAWSa : forall Hp, RTlaws B (fun inst ly S W mem md => RGcfLaws.ARXqA B Hp inst ly S W mem md) (aowned B).
Hypothesis LAWSm : forall Hp, RTlaws B (fun inst ly S W mem md => RGcfLaws.ARXqA B Hp inst ly S W mem md) (AOXm_cf B).

Local Abbreviation ARXA := (fun (Hp : list Z) (inst : Z) (ly : alayout) (S : astate) (W : world tfibsegs)
  (mem : word -> option byte) (md : Model) => RGcfLaws.ARXqA B Hp inst ly S W mem md).

Theorem rw_ret_A : forall ly S Hp Hp' W regs mem md p n_old n ch q ly2 S2 W4 inst so bp regsD memD mdD ly3 S3 W5 regs5 mem5 md5,
  YGcfReallocCompose.rentry_cf tfibsegs B ly S Hp W regs mem md p n_old n ch ->
  K3A B ly S Hp W regs mem md p n_old n ch q ly2 S2 W4 regsD memD mdD ->
  YGcfReallocCompose.realloc_dpre_cf tfibsegs B 1 ARXA Hp inst so bp ly2 S2 W4 regsD memD mdD p n_old
    (YGcfReallocCompose.rtr_cf ly regs ch) ->
  free_dpost_cf tfibsegs B ARXA Hp' inst ly2 S2 W4 regsD memD mdD
    (fun a => p <> PNull /\ sptr_addr B ly2 p <= a < sptr_addr B ly2 p + req_size n_old) ly3 S3 W5 regs5 mem5 md5 ->
  qtight S3 ->
  SRr tfibsegs W5 (cfg_at tfibsegs (raZ regsD) regs5 mem5 md5)
  (fun W' c' => exists regs' mem' md',
    c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\
    getr regs' 10 = w64 (sptr_addr B ly2 q) /\
    ARXA Hp' inst ly3 S3 W' mem' md' /\ same_io md5 md' /\
    RGtop.rkeep tfibsegs B regs W5 mem5 W' mem' /\ RGtop.rwin tfibsegs regs W' mem' /\
    errno_kept_cf B mem5 mem').
Proof using TB LAWSa LAWSm.
intros ly S Hp Hp' W regs mem md p n_old n ch q ly2 S2 W4 inst so bp regsD memD mdD ly3 S3 W5 regs5 mem5 md5 ENT HK3 DPR DPO LP3.
pose proof (rt_errno B TB) as HERR.
unfold YGcfReallocCompose.rentry_cf, acall_pre_cf in ENT.
destruct ENT as ((ARC0 & Hra & Hsp16 & Hlo & Hbot & Hhi & HWIN & Hgp & Htp & HCH & _) & HBLK & HA0 & HNH & HA1 & HN & HL & HU).
unfold K3A, K3r in HK3. destruct HK3 as (KSP & K1d & K20 & KK & KF & KRR & KW & (Eslo & Eshi & Etop) & QB).
unfold YGcfReallocCompose.realloc_dpre_cf, DeallocG.dealloc_pre in DPR. cbv beta in DPR.
pose proof (proj1 DPR) as ARXD.
pose proof (rt_inst B TB _ _ _ _ _ _ _ ARXD) as EI. subst inst.
assert (DBLK : p = PNull \/ In (p, n_old) (blocks S2)) by (clear - DPR; tauto).
unfold free_dpost_cf, dealloc_post_raw in DPO. destruct DPO as (ARX3 & LLE3 & WLE3 & PRS & SIO & FR5 & FR5w & PR5).
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
assert (RAD : raZ regsD = RT_RA_D) by (unfold raZ; rewrite K1d; unfold w64; apply YP03.unsigned_lit_small; unfold RT_RA_D; lia).
assert (STKV : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ (sp0 - 2208 - 8192 <= a < sp0 - 2208) ->
  aview tfibsegs (w_H W5) mem5 a = aview tfibsegs (w_H W4) memD a).
{ intros a Ha Hge. apply FR5.
  - lia.
  - exact (proj1 (STKD a ltac:(rewrite Eslo, Eshi; exact Ha))).
  - exact (proj1 (STK5 a ltac:(rewrite Eslo3, Eshi3, Eslo, Eshi; exact Ha))).
  - unfold ascratch. rewrite HERR. intros [X|X]; [rewrite KSP in X; unfold DFSTACK_G in X; lia | unfold RT_ERRNO in X; lia].
  - apply PB. lia. }
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
intros i _; apply MEQ.
Qed.
End b.
End a.
