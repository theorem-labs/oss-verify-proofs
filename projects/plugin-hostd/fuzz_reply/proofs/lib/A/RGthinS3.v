(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-29: copied from proofs/omx-clap-core/fuzz_preset/lib/A/RGthinS3.v (hub 9f4806388ad, blob 60334f77604b) rt_seg_ret, restated as YGcfReallocCompose.wrap_realloc_walk_cf's field rw_ret at image A (entry facts rentry_cf, Deallocate's post at any ghost set, errno / memnorm kept). *)
(* Modified by Theorem Labs, 2026-10-31: field round 3 part 3c (the record's segments no longer keep the overlay normal
   form): rw_ret_A's memnorm conjunct and its proof removed. *)
(* Modified by Theorem Labs, 2026-10-31: rw_ret_A takes the form of the realloc keep record's field rwk_ret
   (YGcfReallocComposeKeep.wrap_realloc_walk_keep_cf): the memnorm keep right after RGtop.rwin, proved by
   RGcfSegs2a.memnorm_pw (m3 leaves memory unchanged). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/RGcfSegs3.v, with its module paths and module names changed; 36 of its 127 lines of code are new or changed and 56 lines of the source are left out. *)
(* Modified by a Theorem Labs lane (ReallocPrimary.RealSegA), 2026-10-30: from proofs/plugin-hostd/fuzz_reply/lib/A/RGthinS3.v (commit 66a127cb11e, sha256 7d851e4e992d; internal record, reply A text, no relocation) with the statement edits preset A5 made to its copy (a Theorem Labs lane, commit d0fcb396eee): the assert PB follows rl_stack's weakened bound (ASAN_CEIL <= a); module paths: lib.Reusable -> lib.A for AllocG DeallocG ReallocG RGtop. *)
(* fuzz_reply.asan: the thin segment S3 (RGtop.seg_ret): Deallocate's return into Reallocate -> realloc's return
   with a0 = the new block, over the machine run RGthinM2.m3 (the epilogues of Reallocate, asan_realloc and the
   interceptor; ported from cgif_rgb's YF78.v:437 succ_leaf, relocated to fuzz_reply's image). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AllocG DeallocG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ReallocG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import RGtop.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import RGthinK RGthinM RGthinM2 RGthinS.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YP03.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section b.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variable ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable nmax lmax : Z.
Variable lpost : astate -> Prop.
Variable fpre : alayout -> astate -> world tfibsegs -> (word -> option byte) -> sptr -> Z -> Prop.
Variable rU : list Z -> astate -> Prop.
Variable RSTACK : Z.
Variable rpreD : astate -> Z -> Prop.
Hypothesis LAWS : RTlaws B ARX AOX.
Hypothesis HERR : as_errno B = RT_ERRNO.

Theorem rt_seg_ret : seg_ret tfibsegs B U ARX AOX rpre nmax lmax lpost fpre rU RSTACK rpreD RT_PC0 RT_INST (K3r B).
Proof.
unfold seg_ret.
intros ly S W regs mem md p n_old n ch q ly2 S2 W4 so bp regsD memD mdD ly3 S3 W5 regs5 mem5 md5 ENT HK3 DPR DPO LP3.
unfold rentry, realloc_pre in ENT.
destruct ENT as ((ARX0 & Hra & Hsp16 & Hlo & Hbot & Hhi & HWIN & Hgp & Htp & HCH) & RP & HBLK & HFP & HA0 & HA1 & HN & HL & HU).
unfold K3r in HK3. destruct HK3 as (KSP & K1d & K20 & KK & KF & KRR & KW & (Eslo & Eshi & Etop) & QB).
pose proof (proj1 DPR) as ARXD.
assert (DBLK : p = PNull \/ In (p, n_old) (blocks S2))
  by (clear - DPR; unfold DeallocG.dealloc_pre in DPR; tauto).
unfold dealloc_post in DPO. destruct DPO as (ARX3 & LLE3 & WLE3 & PRS & SIO & FR5 & FR5w & PR5).
set (sp0 := spZ regs) in *. set (qa := sptr_addr B ly2 q) in *.
destruct LLE3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop3 & Eslo3 & Eshi3 & _).
pose proof (fun a => rl_stack _ _ _ LAWS ly2 S2 W4 memD mdD a ARXD) as STKD.
pose proof (fun a => rl_stack _ _ _ LAWS ly3 S3 W5 mem5 md5 a ARX3) as STK5.
pose proof (proj2 (rl_stack _ _ _ LAWS ly S W mem md (ly_stk_lo ly) ARX0 ltac:(unfold ASTACK in Hlo; lia))) as SLO.
pose proof (rl_stkhi _ _ _ LAWS ly S W mem md ARX0) as SHI. unfold kHighMemEnd in SHI.
pose proof (proj1 ASAN_CEIL_range) as CR. unfold ASTACK in Hlo, HWIN.
assert (PB : forall a, ASAN_CEIL <= a -> ~ (p <> PNull /\ sptr_addr B ly2 p <= a < sptr_addr B ly2 p + req_size n_old)).
{ intros a Ha [Hne Hin]. destruct DBLK as [HP|HP]; [exact (Hne HP)|].
  destruct (rl_blk _ _ _ LAWS ly2 S2 W4 memD mdD p n_old ARXD HP) as (_ & X2 & _). lia. }
assert (RAD : raZ regsD = RT_RA_D) by (unfold raZ; rewrite K1d; unfold w64; apply YP03.unsigned_lit_small; unfold RT_RA_D; lia).
(* Deallocate changed nothing at or above its entry sp inside the stack *)
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
(* the five words Reallocate saved below its own ra *)
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
{ apply (rl_write _ _ _ LAWS ly3 S3 W5 mem5 md5 mem' _ ARX3); [intros x _ _ _; apply MEQ | intros a _ Hv; rewrite (aview_pw _ mem5 mem' a MEQ); exact Hv | apply sbm_wvb]. }
split; [apply same_io_wvb|].
split; [unfold rkeep; split; [intros a _ _; apply aview_pw; exact MEQ | intros x _; exact (MEQ x)]|].
unfold rwin. intros a Ha. fold sp0 in Ha. unfold ASTACK in Ha. apply (apresent_pw _ mem5 mem' a MEQ). apply PW5. lia.
Qed.
End b.
End a.
