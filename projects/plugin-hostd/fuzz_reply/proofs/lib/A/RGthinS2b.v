(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-29: copied from proofs/omx-clap-core/fuzz_preset/lib/A/RGthinS2b.v (hub 9f4806388ad, blob 1fd765b7cc59) rt_seg_mid_b, restated as YGcfReallocCompose.wrap_realloc_walk_cf's field rw_mid_b at image A (entry facts rentry_cf, Deallocate's pre realloc_dpre_cf, errno / memnorm kept). *)
(* Modified by Theorem Labs, 2026-10-31: field round 3 part 3c (the record's segments no longer keep the overlay normal
   form): rw_mid_b_A's memnorm conjunct and its proof removed. *)
(* Modified by Theorem Labs, 2026-10-31: rw_mid_b_A takes the form of the realloc keep record's field rwk_mid_b
   (YGcfReallocComposeKeep.wrap_realloc_walk_keep_cf): the memnorm keep right after RGtop.rwin, proved by
   RGcfSegs2a.memnorm_pw (m2b leaves memory unchanged). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/RGcfSegs2b.v, with its module paths and module names changed; 37 of its 139 lines of code are new or changed and 59 lines of the source are left out. *)
(* Modified by a Theorem Labs lane (ReallocPrimary.RealSegA), 2026-10-30: from proofs/plugin-hostd/fuzz_reply/lib/A/RGthinS2b.v (commit 66a127cb11e, sha256 2da9e759f416; internal record, reply A text, no relocation); module paths: lib.Reusable -> lib.A for AllocG DeallocG ReallocG RGtop; no other change. *)
(* fuzz_reply.asan: the thin segment S2b (RGtop.seg_mid_b): REAL(memcpy)'s return -> Reallocate's `jal Deallocate`,
   over the machine run RGthinM.m2b (ported from cgif_rgb's YF67.v:43 c1_tail after its memcpy call and YF78.v's
   c2_arm frame, relocated to fuzz_reply's image). *)
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
Variable fpre : alayout -> astate -> world tfibsegs -> (word -> option byte) -> sptr -> Z -> Prop.
Variable rU : list Z -> astate -> Prop.
Variable RSTACK : Z.
Variable rpreD : astate -> Z -> Prop.
Hypothesis LAWS : RTlaws B ARX AOX.
Hypothesis HERR : as_errno B = RT_ERRNO.
Hypothesis HTP : as_tp B = RT_TP.
(* Reallocate frees the old block right after copying out of it; [fpre] is the free call site's premise, which
   cgif instantiates to True. *)
Hypothesis HFPRE : forall ly S W mem p n, fpre ly S W mem p n.

Theorem rt_seg_mid_b : seg_mid_b tfibsegs B U ARX rpre nmax lmax fpre rU RSTACK rpreD RT_PC0 RT_INST RT_PCD
  (K2r B ARX) (K3r B).
Proof.
unfold seg_mid_b.
intros ly S W regs mem md p n_old n ch q ly2 S2 W3 regsM memM mdM regs3 mem3 md3 ENT HK2 HB2 RD2 HU2 PRS SBM CPY FR3 PRE3.
unfold rentry, realloc_pre in ENT.
destruct ENT as ((ARX0 & Hra & Hsp16 & Hlo & Hbot & Hhi & HWIN & Hgp & Htp & HCH) & RP & HBLK & HFP & HA0 & HA1 & HN & HL & HU).
unfold K2r in HK2.
destruct HK2 as (KSP & K1m & K8 & K9 & K18 & K20 & KK & KF & KRR & KW & ARX2 & LAYP & HQB & (Eslo & Eshi & Etop) & KBOT & bp & SO).
set (sp0 := spZ regs) in *. set (qa := sptr_addr B ly2 q) in *. set (pa := sptr_addr B ly p) in *.
unfold so_ok in SO. destruct SO as (So1 & So2 & So3 & Sb1 & Sb2 & Sb3 & Str & Vso & Vlen & Vbuf).
pose proof (rl_blk _ _ _ LAWS ly2 S2 W3 memM mdM q n ARX2 HQB) as BLKQ. fold qa in BLKQ.
destruct BLKQ as (Q1 & Q2 & _ & Q4 & _).
pose proof (proj2 (rl_stack _ _ _ LAWS ly S W mem md (ly_stk_lo ly) ARX0 ltac:(unfold ASTACK in Hlo; lia))) as SLO.
pose proof (rl_stkhi _ _ _ LAWS ly S W mem md ARX0) as SHI. unfold kHighMemEnd in SHI.
pose proof (proj1 ASAN_CEIL_range) as CR. unfold MALLOC_MAX in Q4. unfold ASTACK in Hlo, HWIN.
assert (RSn : 1 <= req_size n /\ n <= req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
assert (RAM : raZ regsM = RT_RA_M) by (unfold raZ; rewrite K1m; unfold w64; apply YP03.unsigned_lit_small; unfold RT_RA_M; lia).
(* the memcpy wrote only inside the new block, which is below the stack *)
assert (MEQ3 : forall a (k : nat), ly_stk_lo ly <= a -> a + Z.of_nat k <= ly_stk_hi ly ->
  mem3 (Z_to_bv 64 (a + Z.of_nat k)) = memM (Z_to_bv 64 (a + Z.of_nat k))).
{ intros a k H1 H2. apply FR3. rewrite YP03.unsigned_lit_small by lia. fold qa. lia. }
assert (XF : forall a v, ly_stk_lo ly <= a -> a + 8 <= ly_stk_hi ly ->
  val_mem tfibsegs (mrestrict (w_H W3) memM) a 8 v -> val_mem tfibsegs (mrestrict (w_H W3) mem3) a 8 v).
{ intros a v H1 H2 V. apply (val_mem_raw _ memM mem3 a 8 v); [|exact V]. intros k Hk. apply MEQ3; lia. }
rewrite RAM. unfold cfg_at at 1.
eapply SRr_mono; [apply (m2b W3 md3 regs3 mem3)|].
intros W' c' _ POST. destruct POST as (EW & regsD & memD & mat & Ec & MEQ & D1 & D10 & D11 & D12 & D13 & D14 & D15 & DK). subst W' c'.
assert (DKg : forall (k : Z) (r : bv 5), In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> acallee_saved k ->
  bv_unsigned r = k -> getr regsD r = getr regsM r).
{ intros k r Hr Hk Hrk. rewrite (DK r Hr). exact (ap_get regsM regs3 k r PRS Hk Hrk). }
assert (DSP : spZ regsD = sp0 - 2208)
  by (unfold spZ; rewrite (DKg 2 2%bv ltac:(cbn; tauto) ltac:(unfold acallee_saved; lia) eq_refl); exact KSP).
assert (D11' : getr regsD 11 = w64 pa)
  by (rewrite D11, (ap_get regsM regs3 9 9%bv PRS ltac:(unfold acallee_saved; lia) eq_refl), K9; exact HA0).
assert (D14' : getr regsD 14 = w64 (sp0 - 2136))
  by (rewrite D14, (ap_get regsM regs3 8 8%bv PRS ltac:(unfold acallee_saved; lia) eq_refl); exact K8).
assert (D10' : getr regsD 10 = w64 RT_INST)
  by (rewrite D10, (ap_get regsM regs3 18 18%bv PRS ltac:(unfold acallee_saved; lia) eq_refl); exact K18).
assert (MEM : forall a (k : nat), ly_stk_lo ly <= a -> a + Z.of_nat k <= ly_stk_hi ly ->
  memD (Z_to_bv 64 (a + Z.of_nat k)) = memM (Z_to_bv 64 (a + Z.of_nat k)))
  by (intros a k H1 H2; rewrite MEQ; apply MEQ3; lia).
assert (XFD : forall a v, ly_stk_lo ly <= a -> a + 8 <= ly_stk_hi ly ->
  val_mem tfibsegs (mrestrict (w_H W3) memM) a 8 v -> val_mem tfibsegs (mrestrict (w_H W3) memD) a 8 v).
{ intros a v H1 H2 V. apply (val_mem_raw _ memM memD a 8 v); [|exact V]. intros k Hk. apply MEM; lia. }
assert (ARXD : ARX RT_INST ly2 S2 W3 memD md3).
{ apply (rl_write _ _ _ LAWS ly2 S2 W3 memM mdM memD md3 ARX2).
  - intros x _ _ Hb. rewrite MEQ. apply FR3. intros Hx. apply Hb. exists q, n. split; [exact HQB|]. fold qa. lia.
  - intros a Ha Hv. rewrite (aview_pw _ mem3 memD a MEQ).
    destruct (Z_lt_le_dec a qa) as [L|L]; [|destruct (Z_lt_le_dec a (qa + Z.min (req_size n_old) n)) as [L2|L2]].
    + rewrite (aview_same _ memM mem3 a); [exact Hv|]. apply FR3. rewrite YP03.unsigned_lit_small by lia. lia.
    + replace a with (qa + (a - qa)) by lia. rewrite (CPY (a - qa) ltac:(lia)). apply apresent_vis.
      destruct (rl_blk _ _ _ LAWS ly2 S2 W3 memM mdM p n_old ARX2 HB2) as (_ & _ & _ & _ & P5 & _).
      rewrite LAYP in P5. fold pa. apply (proj1 (P5 (pa + (a - qa)) ltac:(lia))).
    + rewrite (aview_same _ memM mem3 a); [exact Hv|]. apply FR3. rewrite YP03.unsigned_lit_small by lia. lia.
  - exact SBM. }
destruct KF as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
exists (sp0 - 2136), bp, regsD, memD, (with_vm_backing (m_vm_lazy md3) mat md3).
split; [unfold cfg_at; reflexivity|].
split.
{ unfold DeallocG.dealloc_pre.
  split. { apply (rl_write _ _ _ LAWS ly2 S2 W3 memD md3 memD _ ARXD); [intros x _ _ _; reflexivity | intros a _ Hv; exact Hv | apply sbm_wvb]. }
  split; [exact RD2|].
  split. { rewrite D1. unfold YK0s.ret_ok. vm_compute. reflexivity. }
  split. { unfold raZ. rewrite D1. unfold w64. rewrite YP03.unsigned_lit_small by (unfold RT_RA_D; lia). unfold RT_RA_D. lia. }
  split; [rewrite DSP; unfold sp0 in *; lia|].
  split; [rewrite DSP, Eslo; unfold DFSTACK_G; lia|].
  split; [rewrite DSP; unfold ly_bot in *; rewrite Etop; exact KBOT|].
  split; [rewrite DSP; lia|].
  split. { intros a Ha. rewrite DSP in Ha. unfold DFSTACK_G in Ha. apply (apresent_pw _ mem3 memD a MEQ). apply PRE3.
    apply KW. unfold ASTACK. fold sp0. lia. }
  split. { rewrite (DKg 3 3%bv ltac:(cbn; tauto) ltac:(unfold acallee_saved; lia) eq_refl), (KK 3%bv ltac:(cbn; tauto)). exact Hgp. }
  split. { rewrite (DKg 4 4%bv ltac:(cbn; tauto) ltac:(unfold acallee_saved; lia) eq_refl), (KK 4%bv ltac:(cbn; tauto)). exact Htp. }
  split; [exact D10'|]. split; [rewrite D11', LAYP; reflexivity|]. split; [exact D12|]. split; [exact D13|].
  split; [exact D14'|]. split; [exact D15|].
  split; [rewrite DSP; lia|]. split; [rewrite Eshi; lia|]. split; [clear - Hsp16; Z.div_mod_to_equations; lia|].
  split; [rewrite DSP; lia|]. split; [rewrite Eshi; lia|]. split; [exact Sb3|]. split; [exact Str|].
  split; [apply XFD; [lia | rewrite Eshi in So2; lia | exact Vso]|].
  split; [apply XFD; [lia | rewrite Eshi in So2; lia | exact Vlen]|].
  split. { intros i Hi. apply XFD; [lia | rewrite Eshi in Sb2; lia | exact (Vbuf i Hi)]. }
  split; [exact HU2|]. split; [right; exact HB2 | apply HFPRE]. }
split; [apply same_io_wvb|].
split; [unfold rin; rewrite DSP; unfold ASTACK, DFSTACK_G; fold sp0; lia|].
split. { unfold rkeep. split; [intros a _ _; apply aview_pw; exact MEQ | intros x _; exact (MEQ x)]. }
split. { unfold rwin. intros a Ha. fold sp0 in Ha. unfold ASTACK in Ha. apply (apresent_pw _ mem3 memD a MEQ).
  apply PRE3. apply KW. unfold ASTACK. fold sp0. lia. }
unfold K3r.
split; [exact DSP|]. split; [exact D1|].
split. { rewrite (DKg 20 20%bv ltac:(cbn; tauto) ltac:(unfold acallee_saved; lia) eq_refl). exact K20. }
split.
{ intros r Hr. rewrite <- (KK r Hr). cbn [In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
  (lazymatch goal with |- getr _ ?rr = _ => let k := eval vm_compute in (bv_unsigned rr) in
    apply (DKg k rr); [cbn; tauto | unfold acallee_saved; lia | reflexivity] end). }
split.
{ unfold rt_frames. fold sp0. repeat split; (apply XFD; [lia | lia | assumption]). }
split; [apply XFD; [lia | lia | exact KRR]|].
split. { unfold rwin. intros a Ha. fold sp0 in Ha. unfold ASTACK in Ha. apply (apresent_pw _ mem3 memD a MEQ).
  apply PRE3. apply KW. unfold ASTACK. fold sp0. lia. }
split; [unfold stk_same; split; [exact Eslo | split; [exact Eshi | exact Etop]]|].
fold qa. lia.
Qed.
End b.
End a.
