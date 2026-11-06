(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-29: copied from proofs/omx-clap-core/fuzz_preset/lib/A/RGthinS2a.v (hub 9f4806388ad, blob 0b8806fe7195) rt_seg_mid_a, restated as YGcfReallocCompose.wrap_realloc_walk_cf's field rw_mid_a at image A (entry facts rentry_cf, Allocate's post at AOXm_cf, errno / memnorm kept). *)
(* Modified by Theorem Labs, 2026-10-31: field round 3 part 3c (the record's segments no longer keep the overlay normal
   form): rw_mid_a_A's memnorm conjunct and its proof removed, and with them the memnorm lemmas memnorm_pw /
   memnorm_se, which only the segments' memnorm keeps used. *)
(* Modified by Theorem Labs, 2026-10-31: rw_mid_a_A takes the form of the realloc keep record's field rwk_mid_a
   (YGcfReallocComposeKeep.wrap_realloc_walk_keep_cf): the memnorm keep right after RGtop.rkeep, proved by memnorm_pw
   (m2a leaves memory unchanged); memnorm_pw / memnorm_se restored as they were before the part-3c re-fit. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/RGcfSegs2a.v, with its module paths and module names changed; 35 of its 154 lines of code are new or changed and 97 lines of the source are left out. *)
(* Modified by a Theorem Labs lane (ReallocPrimary.RealSegA), 2026-10-30: from proofs/plugin-hostd/fuzz_reply/lib/A/RGthinS2a.v (commit 66a127cb11e, sha256 a27090cbd6cd; internal record, reply A text, no relocation); module paths: lib.Reusable -> lib.A for AllocG DeallocG ReallocG RGtop; no other change. *)
(* fuzz_reply.asan: the thin segment S2a (RGtop.seg_mid_a): Allocate's return into Reallocate with a block ->
   REAL(memcpy)'s entry, over the machine run RGthinM.m2a (ported from cgif_rgb's YF67.v:156 c1_copy and YF78.v:263
   c1_at_mid, relocated to fuzz_reply's image). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import RGthinK RGthinM RGthinS.
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
Variable rpreA rpreD : astate -> Z -> Prop.
Hypothesis LAWS : RTlaws B ARX AOX.
Hypothesis HERR : as_errno B = RT_ERRNO.

Lemma req_size_rng : forall x, 0 <= x -> 1 <= req_size x /\ x <= req_size x /\ req_size x <= x + 1.
Proof. intros x Hx. unfold req_size. destruct (Z.eqb_spec x 0); lia. Qed.

Theorem rt_seg_mid_a : seg_mid_a tfibsegs B U ARX AOX rpre nmax lmax lpost fpre rU RSTACK rpreA rpreD RT_PC0 RT_INST RT_PCM
  (K1r B) (K2r B ARX).
Proof.
unfold seg_mid_a.
intros ly S W regs mem md p n_old n ch S1 W1 so bp regsA memA mdA q ly2 S2 W2 regs2 mem2 md2
  ENT HK1 APR APO A02 HQ HQB HQP LP2 HB1 HB2 RD2.
unfold rentry, realloc_pre in ENT. destruct ENT as ((ARX0 & Hra & Hsp16 & Hlo & Hbot & Hhi & HWIN & Hgp & Htp & HCH) & RP & HBLK & HFP & HA0 & HA1 & HN & HL & HU).
unfold K1r in HK1. destruct HK1 as (KSP & K1ra & K8 & K13 & K9 & K18 & K19 & KK & KF & KRR & KW & KB).
unfold alloc_pre in APR.
destruct APR as (ARX1 & RA1 & Hra1 & Hra4k & Hsp1 & Hlo1 & Hbot1 & Hhi1 & HW1 & Hgp1 & Htp1 & A10 & A11 & A12 & A13 & A14 & A15 &
  Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htr & Vso & Vlen & Vbuf & HU1 & Hn1 & Hl1).
unfold alloc_post in APO. destruct APO as (ARX2 & LLE & WLE & PRS & SIO & FR2 & FR2w & PR2).
set (sp0 := spZ regs) in *. set (pa := sptr_addr B ly p) in *. set (qa := sptr_addr B ly2 q) in *.
pose proof (rl_layout _ _ _ LAWS ly S1 W1 memA mdA ly2 p n_old ARX1 LLE HB1) as LAYP. fold pa in LAYP.
destruct LLE as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof (rl_blk _ _ _ LAWS ly2 S2 W2 mem2 md2 p n_old ARX2 HB2) as BLKP. rewrite LAYP in BLKP.
destruct BLKP as (P1 & P2 & P3 & P4 & P5 & PH0 & PH2 & PH4).
pose proof (rl_blk _ _ _ LAWS ly S1 W1 memA mdA p n_old ARX1 HB1) as BLKP1. fold pa in BLKP1.
destruct BLKP1 as (_ & _ & _ & _ & P5' & _).
pose proof (rl_blk _ _ _ LAWS ly2 S2 W2 mem2 md2 q n ARX2 HQB) as BLKQ. fold qa in BLKQ.
destruct BLKQ as (Q1 & Q2 & Q3 & Q4 & Q5 & _).
pose proof (rl_disj _ _ _ LAWS ly2 S2 W2 mem2 md2 p n_old q n ARX2 HB2 HQB (fun E => HQP (eq_sym E))) as DISJ.
rewrite LAYP in DISJ. fold qa in DISJ.
pose proof (rl_const _ _ _ LAWS ly2 S2 W2 mem2 md2 ARX2) as (VC1 & VC2).
pose proof (fun a => rl_stack _ _ _ LAWS ly S1 W1 memA mdA a ARX1) as STK1. pose proof (fun a => rl_stack _ _ _ LAWS ly2 S2 W2 mem2 md2 a ARX2) as STK2.
unfold ASTACK in Hlo, HWIN.
pose proof (proj2 (rl_stack _ _ _ LAWS ly S W mem md (ly_stk_lo ly) ARX0 ltac:(lia))) as SLO.
pose proof (rl_stkhi _ _ _ LAWS ly S W mem md ARX0) as SHI. unfold kHighMemEnd in SHI.
pose proof (proj1 ASAN_CEIL_range) as CR.
pose proof (req_size_rng n_old ltac:(unfold MALLOC_MAX in P4; lia)) as RSo.
pose proof (req_size_rng n ltac:(unfold MALLOC_MAX in Q4; lia)) as RSn.
unfold MALLOC_MAX in P4, Q4.
assert (RAA : raZ regsA = RT_RA_A) by (unfold raZ; rewrite K1ra; unfold w64; apply YP03.unsigned_lit_small; unfold RT_RA_A; lia).
assert (G9 : getr regs2 9 = w64 pa) by (rewrite (ap_get regsA regs2 9 9%bv PRS ltac:(unfold acallee_saved; lia) eq_refl), K9; exact HA0).
assert (G19 : getr regs2 19 = w64 n) by (rewrite (ap_get regsA regs2 19 19%bv PRS ltac:(unfold acallee_saved; lia) eq_refl), K19; exact HA1).
assert (SOE : so = sp0 - 2136).
{ apply w64_inj; [unfold spZ in *; lia | unfold sp0, spZ in *; lia |]. rewrite <- A13. exact K13. }
subst so.
(* the stack bytes outside Allocate's window and the old block's bytes are Allocate's frame *)
assert (STKV : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ (sp0 - 2208 - 4096 <= a < sp0 - 2208) ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W1) memA a).
{ intros a Ha Hn. apply FR2.
  - lia.
  - exact (proj1 (STK1 a Ha)).
  - apply (proj1 (STK2 a ltac:(rewrite Eslo, Eshi; exact Ha))).
  - unfold ascratch. rewrite HERR. intros [X|X]; [rewrite KSP in X; unfold AFSTACK_G in X; lia | unfold RT_ERRNO in X; lia].
  - intros [_ X]. lia. }
assert (BLKV : forall a, pa <= a < pa + req_size n_old -> aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W1) memA a).
{ intros a Ha. apply FR2.
  - lia.
  - exact (proj1 (proj2 (P5' a Ha))).
  - exact (proj1 (proj2 (P5 a Ha))).
  - unfold ascratch. rewrite HERR. intros [X|X]; [rewrite KSP in X; unfold AFSTACK_G in X; lia | exact (proj2 (proj2 (P5 a Ha)) X)].
  - intros [_ X]. lia. }
assert (XF : forall a v, ly_stk_lo ly <= a -> a + 8 <= ly_stk_hi ly -> sp0 - 2208 <= a ->
  val_mem tfibsegs (mrestrict (w_H W1) memA) a 8 v -> val_mem tfibsegs (mrestrict (w_H W2) mem2) a 8 v).
{ intros a v H1 H2 H3 V. apply (val_mem_xfer (w_H W1) (w_H W2) memA mem2 a 8 v); [|exact V].
  intros k Hk. apply STKV; lia. }
rewrite RAA. unfold cfg_at at 1.
eapply SRr_mono.
{ apply (m2a W2 md2 regs2 mem2 pa qa n (req_size n_old) G9 A02 G19); [lia | lia | lia | lia | lia | exact PH0 | exact PH2 | exact PH4 | exact VC1 | exact VC2]. }
intros W' c' _ POST. destruct POST as (EW & regsM & memM & mat & Ec & MEQ & M1 & M10 & M11 & M12 & M19 & M20 & MK). subst W' c'.
assert (MKg : forall (k : Z) (r : bv 5), In r [2; 3; 4; 8; 9; 18; 21; 22; 23; 24; 25; 26; 27]%bv -> acallee_saved k -> bv_unsigned r = k ->
  getr regsM r = getr regsA r).
{ intros k r Hr Hk Hrk. rewrite (MK r Hr). exact (ap_get regsA regs2 k r PRS Hk Hrk). }
exists regsM, memM, (with_vm_backing (m_vm_lazy md2) mat md2).
split; [unfold cfg_at; reflexivity|].
split.
{ unfold rmemcpy_pre. rewrite M1, M10, M11, M12, Z.min_comm.
  split; [unfold YK0s.ret_ok; vm_compute; reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split. { intros a Ha. apply apresent_wr. apply (apresent_pw _ mem2 memM a MEQ). exact (proj1 (Q5 a ltac:(lia))). }
  intros a Ha. rewrite (aview_pw _ mem2 memM a MEQ). apply apresent_vis. exact (proj1 (P5 a ltac:(lia))). }
split.
{ intros i Hi. rewrite (aview_pw _ mem2 memM _ MEQ). rewrite BLKV by lia. apply KB. lia. }
split.
{ intros a Ha. split; [lia|]. unfold ascratch. rewrite HERR. intros [X|X]; [unfold ASTACK in X; lia | exact (proj2 (proj2 (Q5 a Ha)) X)]. }
split; [apply same_io_wvb|].
split; [unfold rkeep; split; [intros a _ _; apply aview_pw; exact MEQ | intros x _; exact (MEQ x)]|].
unfold K2r.
split. { unfold spZ. rewrite (MKg 2 2%bv ltac:(cbn; tauto) ltac:(unfold acallee_saved; lia) eq_refl). exact KSP. }
split; [exact M1|].
split. { rewrite (MKg 8 8%bv ltac:(cbn; tauto) ltac:(unfold acallee_saved; lia) eq_refl). exact K8. }
split. { rewrite (MKg 9 9%bv ltac:(cbn; tauto) ltac:(unfold acallee_saved; lia) eq_refl). exact K9. }
split. { rewrite (MKg 18 18%bv ltac:(cbn; tauto) ltac:(unfold acallee_saved; lia) eq_refl). exact K18. }
split; [exact M20|].
split.
{ intros r Hr. rewrite <- (KK r Hr). cbn [In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
  (lazymatch goal with |- getr _ ?rr = _ => let k := eval vm_compute in (bv_unsigned rr) in
    apply (MKg k rr); [cbn; tauto | unfold acallee_saved; lia | reflexivity] end). }
destruct KF as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
split.
{ unfold rt_frames. fold sp0.
  repeat split; (apply (val_mem_pw _ mem2 memM _ _ _ MEQ); apply XF; [lia | lia | lia | assumption]). }
split. { apply (val_mem_pw _ mem2 memM _ _ _ MEQ). apply XF; [lia | lia | lia | exact KRR]. }
split.
{ unfold rwin. intros a Ha. fold sp0 in Ha. unfold ASTACK in Ha. apply (apresent_pw _ mem2 memM a MEQ).
  destruct (Z_lt_le_dec a (sp0 - 2208 - 4096)) as [L|L]; [|destruct (Z_lt_le_dec a (sp0 - 2208)) as [L2|L2]].
  - apply vis_apresent_hi; [unfold TFIB_IMG_END; lia|]. rewrite STKV by lia. apply apresent_vis. apply KW. unfold ASTACK. lia.
  - apply PR2. rewrite KSP. unfold AFSTACK_G. lia.
  - apply vis_apresent_hi; [unfold TFIB_IMG_END; lia|]. rewrite STKV by lia. apply apresent_vis. apply KW. unfold ASTACK. lia. }
split.
{ apply (rl_write _ _ _ LAWS ly2 S2 W2 mem2 md2 memM _ ARX2).
  - intros x _ _ _. apply MEQ.
  - intros a _ Hv. rewrite (aview_pw _ mem2 memM a MEQ). exact Hv.
  - apply sbm_wvb. }
split; [exact LAYP|]. split; [exact HQB|].
split; [unfold stk_same; split; [exact Eslo | split; [exact Eshi | exact Etop]]|].
split; [rewrite KSP in Hbot1; exact Hbot1|].
exists bp. unfold so_ok. rewrite Eshi. fold sp0 in Hso1, Hbp1 |- *. rewrite KSP in Hso1, Hbp1.
split; [lia|]. split; [lia|]. split; [exact Hso3|]. split; [lia|]. split; [lia|]. split; [exact Hbp3|]. split; [exact Htr|].
split. { apply (val_mem_pw _ mem2 memM _ _ _ MEQ). apply XF; [lia | lia | lia | exact Vso]. }
split. { apply (val_mem_pw _ mem2 memM _ _ _ MEQ). apply XF; [lia | lia | lia | exact Vlen]. }
intros i Hi. apply (val_mem_pw _ mem2 memM _ _ _ MEQ). apply XF; [lia | lia | lia | exact (Vbuf i Hi)].
Qed.
End b.
End a.
