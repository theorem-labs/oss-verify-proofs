(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-29: copied from proofs/omx-clap-core/fuzz_preset/lib/A/RGthinS4.v (hub 9f4806388ad, blob ab2a295d7ba3) rt_seg_nret, restated as YGcfReallocCompose.wrap_realloc_walk_cf's field rw_nret at image A (entry facts rentry_cf, errno / oom byte from TfibSyms, memnorm kept). *)
(* Modified by Theorem Labs, 2026-10-31: field round 3 part 3c (the record's segments no longer keep the overlay normal
   form): rw_nret_A's memnorm conjunct and its proof removed. *)
(* Modified by Theorem Labs, 2026-10-31: rw_nret_A takes the form of the realloc keep record's field rwk_nret
   (YGcfReallocComposeKeep.wrap_realloc_walk_keep_cf): the memnorm keep right after RGtop.rwin, proved by
   RGcfSegs2a.memnorm_se (m4 changes only a stack window above the image and errno, which lies in the image's
   writable window). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/RGcfSegs4.v, with its module paths and module names changed; 34 of its 148 lines of code are new or changed and 52 lines of the source are left out. *)
(* Modified by a Theorem Labs lane (ReallocPrimary.RealSegA), 2026-10-30: from proofs/plugin-hostd/fuzz_reply/lib/A/RGthinS4.v (commit 66a127cb11e, sha256 e51e99b48d0e; internal record, reply A text, no relocation); module paths: lib.Reusable -> lib.A for AllocG DeallocG ReallocG RGtop; no other change. *)
(* fuzz_reply.asan: the thin segments S4 (RGtop.seg_nret) and S6 (RGtop.seg_npost):
   - S4: Allocate's return into Reallocate with NULL -> realloc's return with a0 = 0 and errno = ENOMEM, over the
     machine run RGthinM2.m4 (ported from cgif_rgb's YF68.v:104 c_null, relocated to fuzz_reply's image);
   - S6: Allocate's return into asan_realloc (its NULL-input call) -> realloc's return with a0 = the result, over
     RGthinM2.m6a (a block) and RGthinM2.m6b (NULL, errno = ENOMEM). *)
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
Variable rpreA : astate -> Z -> Prop.
Hypothesis LAWS : RTlaws B ARX AOX.
Hypothesis HTP : as_tp B = RT_TP.

(* The out-of-memory byte is in the image, below the stack and apart from errno. *)
Lemma oom_apart : forall a, RT_OOM <= a < RT_OOM + 1 -> ~ (RT_ERRNO <= a < RT_ERRNO + 4).
Proof. intros a Ha. unfold RT_OOM, RT_ERRNO in *. lia. Qed.

Theorem rt_seg_nret : seg_nret tfibsegs B U ARX AOX rpre nmax lmax lpost fpre rU RSTACK rpreA RT_PC0 RT_INST RT_OOM (K1r B).
Proof.
unfold seg_nret.
intros HTIE ly S W regs mem md p n_old n ch S1 W1 so bp regsA memA mdA ly2 S2 W2 regs2 mem2 md2
  ENT HK1 APR APO A02 LP2 OOM HB1 HB2.
(* errno's address: the tie (seg_nret's premise) with the image's tp. *)
assert (HERR : as_errno B = RT_ERRNO) by (rewrite HTIE, HTP; unfold RT_TP, RT_ERRNO; lia).
unfold rentry, realloc_pre in ENT.
destruct ENT as ((ARX0 & Hra & Hsp16 & Hlo & Hbot & Hhi & HWIN & Hgp & Htp & HCH) & RP & HBLK & HFP & HA0 & HA1 & HN & HL & HU).
unfold K1r in HK1. destruct HK1 as (KSP & K1ra & K8 & K13 & K9 & K18 & K19 & KK & KF & KRR & KW & KB).
pose proof (proj1 APR) as ARX1.
unfold alloc_post in APO. destruct APO as (ARX2 & LLE & WLE & PRS & SIO & FR2 & FR2w & PR2).
set (sp0 := spZ regs) in *.
destruct LLE as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof (fun a => rl_stack _ _ _ LAWS ly S1 W1 memA mdA a ARX1) as STK1.
pose proof (fun a => rl_stack _ _ _ LAWS ly2 S2 W2 mem2 md2 a ARX2) as STK2.
pose proof (proj2 (rl_stack _ _ _ LAWS ly S W mem md (ly_stk_lo ly) ARX0 ltac:(unfold ASTACK in Hlo; lia))) as SLO.
pose proof (rl_stkhi _ _ _ LAWS ly S W mem md ARX0) as SHI. unfold kHighMemEnd in SHI.
pose proof (proj1 ASAN_CEIL_range) as CR. unfold ASTACK in Hlo, HWIN.
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
{ apply (rl_write _ _ _ LAWS ly2 S2 W2 mem2 md2 mem' _ ARX2).
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
split; [rewrite HERR; exact MR2|].
apply (val_mem_raw (w_H W2) mem2 mem' RT_OOM 1 1); [|exact OOM].
intros k Hk. apply MR1; rewrite YP03.unsigned_lit_small by (unfold RT_OOM; lia); unfold RT_OOM, RT_ERRNO in *; lia.
Qed.
End b.
End a.
