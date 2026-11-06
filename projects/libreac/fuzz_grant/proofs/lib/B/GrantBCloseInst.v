(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from part of proofs/cgif/cgif_file_fuzzer/lib/A/ACfi.v (link_ML, link_SMP, link_FFL, link_ASF, link_AMEMSET, link_AMEMCPY, tfib_ROB) for libreac/fuzz_grant: the facts are stated at GrantB and at the listing's instance PI_grant, the stack_malloc, bcmp and set_shadow_f5 entries of the memory-checking runtime, the walks' PALib and PALibF records, the shadow of the image and of its registered globals, the image's read-only tables and the image facts of ctrl_finish and reac_ctrl_parse are added; module paths changed. *)
(* Modified by Theorem Labs, 2026-10: adapted from lib/A/Prog/GrantClose.v for image B (fuzz_grant.asan-ubsan). *)
(* The closing instances of image B's walks: every runtime fact RT_* and image fact IMG_* that the closer
   lib/B/Prog/GrantBClose.v and the bridge lib/B/Prog/GrantBTFIB.v take as a named hypothesis, PROVED here at image B's
   own runtime record GrantB (lib/B/YD2l.v:16) and image instance PI_grant (lib/B/Prog/GrantImg.v:152), and the three
   facts of the record (H_universe_B, H_malloc_ra0_B, H_free_ra0_B) by reflexivity. This file proves no function: each
   runtime entry is taken by the B core's realizer of it (lib/B/Y*.v, lib/B/Rt), each image fact by the check lemmas of
   lib/B/Prog/GrantBImgFacts.v and lib/B/Prog/GrantCloseChk.v, run here on GrantB by computation.

   The shape is image A's lib/A/Prog/GrantClose.v (a working branch af735a950e2), fact by fact:
     A (lib/A/Prog/GrantClose.v)        B (here)                      B core theorem used
     grant_LAWS                          grantB_LAWS                   Reusable/YG0q.v AR_laws_ok
     grant_PALib / grant_PALibF          grantB_PALIB / grantB_PALIBF  by computation at GrantB
     grant_ML / grant_SMP                grantB_ML / grantB_SMP        Reusable/YG05.v model_laws_ok / stack_malloc_progress
     grant_FFL / grant_ASF               grantB_FFL / grantB_ASF       AR_laws (al_flag, al_client_img) / YG0t astack_free_law_ok
     (no A twin: A's walks take none)    grantB_TP_FS                  lib/B/Rt/RtTpFs.v rt_tp_fs_of_const
     AF0w / AF0q (AGrantT.v:43-44)       grantB_MALLOC / grantB_FREE   lib/B/YF0w.v tfib_amalloc_realizes / YF0q.v afree_realizes_closed
     grant_AMEMCPY / grant_AMEMSET       grantB_MEMCPY / grantB_MEMSET lib/B/YE2q.v asan_memcpy_realizes / YE2r.v asan_memset_realizes
     grant_ABCMP                         grantB_BCMP                   lib/B/YE2s.v bcmp_icpt_contract
     grant_ASM0 / 1 / 2 / 4              grantB_SM0 / 1 / 2 / 4        lib/B/Rt/StackMalloc0.v / YF0s.v / YF0u.v / StackMalloc4.v stack_malloc<c>_contract
     (image B only)                      grantB_SM6 / grantB_SF6       lib/B/Rt/StackMalloc6.v disco_stack_malloc6 / StackFree6S.v disco_stack_free6_shared
     grant_SSF5                          grantB_SS00 / SSF5 / SSF8     lib/B/Rt/SetShadow.v grantB_set_shadow_00 / f5 / f8
     grant_img_shadow_vis                grantB_IMGSH                  vscan over image B's zero-shadow ranges and shadow cells
     grant_globs_marked                  grantB_GLOBS                  glob_chk over GrantTop.v's GRANT_GLOBS_B
     the table / row / jump-table facts  grantB_IMG_*                  GrantBImgFacts.v's corollaries, ro_free by computation *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK04 YA0i YA0n YP09 YI04 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG05 YG0q YG0t.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YO0f.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import SetShadowDef StackFreeDef.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YF0l YF0m YD2l.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require YCej YF0w YF0q YE2q YE2r YE2s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Rt Require
RtTpFs SetShadow StackMalloc0 YF0s YF0u StackMalloc4 StackMalloc6 StackFree6S.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantFrame GrantRo GrantCloseChk GrantImg GrantBContracts.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require GrantBImgFacts.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import GrantSweepModel GroupaModel.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- closed numeric goals, by computation ------------------------------------------------------------------------ *)
Ltac zchk := lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split; zchk
  | |- _ \/ _ => first [left; zchk | right; zchk]
  | |- ls_apart _ _ _ _ => unfold ls_apart; zchk
  | |- in_zs _ _ _ => apply in_zs_of_b; vm_compute; reflexivity
  | |- Z.le _ _ => apply Z.leb_le; vm_compute; reflexivity
  | |- Z.lt _ _ => apply Z.ltb_lt; vm_compute; reflexivity
  | |- @eq Z _ _ => apply Z.eqb_eq; vm_compute; reflexivity
  end.

(* ---- the checks, by computation on image B ----------------------------------------------------------------------- *)
Lemma grantB_vscan : vscan Tfib_zero_shadow Tfib_const_shadow (Pos.to_nat 4096) (IMG_LO / 8) (IMG_HI / 8) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma grantB_globs_chk : forallb (glob_chk Tfib_zero_shadow Tfib_const_shadow) GRANT_GLOBS_B = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zsB_align_chk : forallb (fun r => (fst r mod 8 =? 0) && (snd r mod 8 =? 0) && (0 <=? snd r))%bool Tfib_zero_shadow = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zsB_align : forall q m, In (q, m) Tfib_zero_shadow -> q mod 8 = 0 /\ m mod 8 = 0 /\ 0 <= m.
Proof.
intros q m Hin. pose proof (proj1 (forallb_forall _ _) zsB_align_chk (q, m) Hin) as Hb. cbn [fst snd] in Hb.
apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.leb_le in H3. auto.
Qed.

(* ro_free (GrantCloseChk.v:240) at image B's record: no byte of [base, base + n) is an owned static of GrantB or a
   byte of its errno cell, checked against GrantB's own lists. *)
Definition ro_free_b (B : asyms) (base n : Z) : bool :=
  (forallb (fun r => (base + n <=? fst r) || (fst r + snd r <=? base)) (as_owned_static B) &&
   ((base + n <=? as_errno B) || (as_errno B + 4 <=? base)))%bool.
Lemma ro_free_of_b : forall B base n, ro_free_b B base n = true -> ro_free B base n.
Proof.
intros B base n H a Ha. unfold ro_free_b in H. apply andb_prop in H as [H1 H2]. split.
- intros HE. apply Exists_exists in HE as (r & Hr & Hz). rewrite forallb_forall in H1. specialize (H1 r Hr).
  unfold in_zr in Hz. apply orb_true_iff in H1 as [H1|H1]; apply Z.leb_le in H1; lia.
- apply orb_true_iff in H2 as [H2|H2]; apply Z.leb_le in H2; lia.
Qed.
Ltac rofree := apply ro_free_of_b; vm_compute; reflexivity.

(* Every address of image B's first PT_LOAD (the read-only one that holds the template 0x211c0) is a byte of the image. *)
Lemma grantB_in_img_seg0 : forall a, 0x10000 <= a < 0x2f000 -> in_img grantsegsB0 a.
Proof.
intros a Ha. unfold in_img. eexists. split; [left; reflexivity|].
match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) =>
  let l := eval vm_compute in lo in let h := eval vm_compute in sz in change lo with l; change sz with h end.
lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- 1. the allocator laws: Reusable/YG0q.v:804 AR_laws_ok holds for every segment list and record ---------------
   (image A's GrantClose.v:69-71 grant_LAWS is the same line at image A's GrantB). *)
Lemma grantB_LAWS : AR_laws grantsegsB0 GrantB.
Proof. exact (AR_laws_ok _ GrantB). Qed.

(* ---- 2. the walks' records PALib and PALibF ----------------------------------------------------------------------- *)
Lemma grantB_api_env : api_env grantsegsB0 GrantB.
Proof.
split; [|split].
- cbn [as_errno GrantB]. unfold TFIB_ERRNO, kLowMemEnd. lia.
- intros a Ha. cbn [as_errno GrantB] in Ha. unfold TFIB_ERRNO in Ha. unfold in_img.
  eexists. split; [do 3 right; left; reflexivity|].
  match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) =>
    let l := eval vm_compute in lo in let h := eval vm_compute in sz in change lo with l; change sz with h end.
  lia.
- split; apply (ts_universe_drv GrantB GrantB_syms);
    cbn [as_code GrantB Tfib_code pc_malloc_ra0 pc_free_ra0 DRV_TRACES In];
    repeat (first [left; reflexivity | right]).
Qed.

Lemma grantB_PALIB : GrantBContracts.RT_PALIB (PI := PI_grant) GrantB.
Proof.
unfold GrantBContracts.RT_PALIB. constructor.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- zchk.
- exact grantB_api_env.
- reflexivity.
- reflexivity.
- zchk.
Qed.

Lemma grantB_PALIBF : GrantBContracts.RT_PALIBF (PI := PI_grant) GrantB.
Proof.
unfold GrantBContracts.RT_PALIBF. constructor.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- cbn [zseps zseps_from fst snd]. zchk.
Qed.

(* ---- 3. the model, the side stack's progress, the frame flags, the frame free, the thread pointer --------------- *)
Lemma grantB_ML : GrantBContracts.RT_ML GrantB.
Proof. exact (model_laws_ok (as_universe GrantB) (ts_universe GrantB GrantB_syms)). Qed.

Lemma grantB_SMP : GrantBContracts.RT_SMP GrantB.
Proof. intros s cid W Hc Hn. exact (stack_malloc_progress (as_universe GrantB) s cid W Hc Hn). Qed.

Lemma grantB_FFL : GrantBContracts.RT_FFL (PI := PI_grant) GrantB.
Proof.
intros ly S W mem md cid pos HAR Hin.
destruct (al_flag _ _ grantB_LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
destruct (al_client_img _ _ grantB_LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof HAR as (M & L & _). pose proof (grant_img_cover ly S md L) as [C1 C2].
rewrite IMG_LO_B_val in C1. rewrite IMG_TOP_B_val in C2.
destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
split; [exact Hp|]. split; [exact Ho|]. split.
- split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
- split; [exact H4096|]. split; [|exact Hceil]. unfold zone2, off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

Lemma grantB_ASF : GrantBContracts.RT_ASF (PI := PI_grant) GrantB.
Proof. exact (astack_free_law_ok _ GrantB). Qed.

(* RT_TP_FS: AR's constant cells hold the thread pointer's word, and image B's Tfib_const_sym holds the cell
   `c8 (ATp 0) (AF 0)` (lib/B/YF0m.v:30). *)
Lemma grantB_TP_FS : GrantBContracts.RT_TP_FS (PI := PI_grant) GrantB.
Proof.
unfold GrantBContracts.RT_TP_FS. apply RtTpFs.rt_tp_fs_of_const.
intros ly. cbn [as_const GrantB]. unfold Tfib_const. apply in_or_app. left.
unfold Tfib_const_sym. repeat (first [left; reflexivity | right]).
Qed.

(* ---- 4. the memory-checking runtime's entries the walks call ------------------------------------------------------ *)
Lemma grantB_MALLOC : GrantBContracts.RT_MALLOC (PI := PI_grant) GrantB.
Proof. exact (YF0w.tfib_amalloc_realizes GrantB GrantB_syms (fun t => eq_refl)). Qed.

Lemma grantB_FREE : GrantBContracts.RT_FREE (PI := PI_grant) GrantB.
Proof. exact (YF0q.afree_realizes_closed GrantB GrantB_syms (fun t => eq_refl)). Qed.

Lemma grantB_sigma_memset : pa_sigma (PAImg := PI_grant) GS___asan_memset = 0x52024.
Proof. reflexivity. Qed.
Lemma grantB_sigma_memcpy : pa_sigma (PAImg := PI_grant) GS___asan_memcpy = 0x51b88.
Proof. reflexivity. Qed.

Lemma grantB_MEMCPY : GrantBContracts.RT_MEMCPY (PI := PI_grant) GrantB.
Proof.
unfold GrantBContracts.RT_MEMCPY. rewrite grantB_sigma_memcpy.
intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull Hsrc.
exact (YE2q.asan_memcpy_realizes GrantB grantB_LAWS GrantB_syms ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull Hsrc).
Qed.

Lemma grantB_MEMSET : GrantBContracts.RT_MEMSET (PI := PI_grant) GrantB.
Proof.
unfold GrantBContracts.RT_MEMSET. rewrite grantB_sigma_memset.
intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull _.
exact (YE2r.asan_memset_realizes GrantB grantB_LAWS GrantB_syms ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Hra Hhull Ham).
Qed.

Lemma grantB_BCMP : GrantBContracts.RT_BCMP (PI := PI_grant) GrantB.
Proof. exact (YE2s.bcmp_icpt_contract GrantB grantB_LAWS GrantB_syms). Qed.

(* __asan_stack_malloc_0 / _1 / _2 / _4 (0x3cf4c / 0x3d0c0 / 0x3d250 / 0x3d3ec): lib/B/Rt/StackMalloc0.v, YF0s.v, YF0u.v,
   StackMalloc4.v (a working branch cce7df57aaa), the B twins of image A's lib/A/Rt/StackMalloc0.v, AF0s.v, AF0u.v,
   StackMalloc4.v. *)
Lemma grantB_SM0 : GrantBContracts.RT_SM (PI := PI_grant) GrantB 0.
Proof. exact (StackMalloc0.stack_malloc0_contract GrantB grantB_LAWS GrantB_syms). Qed.
Lemma grantB_SM1 : GrantBContracts.RT_SM (PI := PI_grant) GrantB 1.
Proof. exact (YF0s.stack_malloc1_contract GrantB grantB_LAWS GrantB_syms). Qed.
Lemma grantB_SM2 : GrantBContracts.RT_SM (PI := PI_grant) GrantB 2.
Proof. exact (YF0u.stack_malloc2_contract GrantB grantB_LAWS GrantB_syms). Qed.
Lemma grantB_SM4 : GrantBContracts.RT_SM (PI := PI_grant) GrantB 4.
Proof. exact (StackMalloc4.stack_malloc4_contract GrantB grantB_LAWS GrantB_syms). Qed.

Lemma grantB_SM6 : GrantBContracts.RT_SM (PI := PI_grant) GrantB 6.
Proof. exact (StackMalloc6.disco_stack_malloc6 fx GrantB grantB_LAWS GrantB_syms). Qed.

Lemma grantB_SF6 : GrantBContracts.RT_SF6 (PI := PI_grant) GrantB.
Proof. exact (StackFree6S.disco_stack_free6_shared fx GrantB grantB_LAWS GrantB_syms). Qed.

Lemma grantB_SS00 : GrantBContracts.RT_SS00 (PI := PI_grant) GrantB.
Proof. exact (SetShadow.grantB_set_shadow_00 GrantB grantB_LAWS GrantB_syms). Qed.
Lemma grantB_SSF5 : GrantBContracts.RT_SSF5 (PI := PI_grant) GrantB.
Proof. exact (SetShadow.grantB_set_shadow_f5 GrantB grantB_LAWS GrantB_syms). Qed.
Lemma grantB_SSF8 : GrantBContracts.RT_SSF8 (PI := PI_grant) GrantB.
Proof. exact (SetShadow.grantB_set_shadow_f8 GrantB grantB_LAWS GrantB_syms). Qed.

(* ---- 5. the shadow of the image and of its registered globals ----------------------------------------------------- *)
(* A shadow cell of the start-up certificate holds its byte in every state. *)
Lemma grantB_shadow_cell : forall ly S (W : world grantsegsB0) mem md s v,
  AR grantsegsB0 GrantB ly S W mem md -> In (z1 (ANum s) v) Tfib_const_shadow ->
  aview grantsegsB0 (w_H W) mem s = Some (YG0f.le_byte v 1 0).
Proof.
intros ly S W mem md s v HAR Hin.
pose proof (am_const _ _ _ _ (proj1 HAR)) as HC. rewrite Forall_forall in HC.
assert (Hin' : In (z1 (ANum s) v) (as_const GrantB ly)).
{ cbn [as_const GrantB]. unfold Tfib_const. apply in_or_app. right. apply in_or_app. right. exact Hin. }
specialize (HC _ Hin'). unfold cell_holds, z1, c1 in HC. cbn [c_at c_val c_w aeval] in HC.
specialize (HC 0%nat ltac:(lia)). cbn [Z.of_nat] in HC. rewrite Z.add_0_r in HC. exact HC.
Qed.

(* A granule of a zero-shadow range of the certificate has shadow byte 0 in every state. *)
Lemma grantB_zs_rd : forall ly S (W : world grantsegsB0) mem md q m j,
  AR grantsegsB0 GrantB ly S W mem md -> In (q, m) Tfib_zero_shadow -> q / 8 <= j < (q + m) / 8 ->
  aview grantsegsB0 (w_H W) mem (SHADOW_OFF + j) = Some 0.
Proof.
intros ly S W mem md q m j HAR Hin Hj.
pose proof (al_zshadow _ _ grantB_LAWS ly S W mem md (q, m) HAR (or_intror Hin)) as Hz. cbn [fst snd] in Hz.
destruct (zsB_align q m Hin) as (Hq & Hm & Hm0).
assert (E : (q + m) / 8 = q / 8 + m / 8).
{ pose proof (Z.div_mod q 8 ltac:(lia)) as Dq.
  replace (q + m) with (m + q / 8 * 8) by lia. rewrite Z.div_add by lia. lia. }
replace (SHADOW_OFF + j) with (shadow_of_addr SHADOW_OFF q + (j - q / 8)) by (unfold shadow_of_addr; lia).
apply Hz. lia.
Qed.

Lemma grantB_IMGSH : GrantBContracts.RT_IMGSH (PI := PI_grant) GrantB.
Proof.
intros ly S W mem md a HAR Ha. unfold shadow_addr.
assert (E8 : 8 * (IMG_HI / 8) = IMG_HI) by (vm_compute; reflexivity).
assert (Hj : IMG_LO / 8 <= a / 8 < IMG_HI / 8).
{ split; [apply Z.div_le_mono; lia | apply Z.div_lt_upper_bound; lia]. }
destruct (vscan_ok _ _ _ _ _ grantB_vscan (a / 8) Hj) as [(q & m & Hin & Hq) | Hc].
- intros Hn. pose proof (eq_trans (eq_sym (grantB_zs_rd ly S W mem md q m (a / 8) HAR Hin Hq)) Hn) as C. discriminate C.
- apply existsb_exists in Hc as (c & Hin & Hb). destruct (is_shc_eq _ _ Hb) as [v ->].
  intros Hn. pose proof (eq_trans (eq_sym (grantB_shadow_cell ly S W mem md _ v HAR Hin)) Hn) as C. discriminate C.
Qed.

Lemma grantB_GLOBS : GrantBContracts.RT_GLOBS (PI := PI_grant) GrantB.
Proof.
intros ly S W mem md q sz Hin HAR.
pose proof (proj1 (forallb_forall _ _) grantB_globs_chk (q, sz) Hin) as Hb. unfold glob_chk in Hb. cbn [fst snd] in Hb.
apply andb_prop in Hb as [Hb Hlast]. apply andb_prop in Hb as [Hb Hfull]. apply andb_prop in Hb as [Hq Hsz].
apply Z.eqb_eq in Hq. apply Z.leb_le in Hsz.
apply existsb_exists in Hfull as ([r0 m0] & Hr & Hf). cbn [fst snd] in Hf.
apply andb_prop in Hf as [Hf1 Hf2]. apply Z.leb_le in Hf1. apply Z.leb_le in Hf2.
destruct (zsB_align r0 m0 Hr) as (Hr8 & Hm8 & Hm0).
split; [exact Hq|]. split; [exact Hsz|]. intros i Hi.
pose proof (Z.div_mod q 8 ltac:(lia)) as Dq. pose proof (Z.div_mod r0 8 ltac:(lia)) as Dr.
pose proof (Z.div_mod sz 8 ltac:(lia)) as Ds. pose proof (Z.mod_pos_bound sz 8 ltac:(lia)) as Bs.
pose proof (Z.div_mod (sz + 7) 8 ltac:(lia)) as Ds7. pose proof (Z.mod_pos_bound (sz + 7) 8 ltac:(lia)) as Bs7.
pose proof (Z.div_mod (r0 + m0) 8 ltac:(lia)) as Drm. pose proof (Z.mod_pos_bound (r0 + m0) 8 ltac:(lia)) as Brm.
destruct (i <? sz / 8) eqn:Hlt.
- apply Z.ltb_lt in Hlt. unfold shadow_of_addr.
  replace (SHADOW_OFF + q / 8 + i) with (SHADOW_OFF + (q / 8 + i)) by lia.
  apply (grantB_zs_rd ly S W mem md r0 m0); [exact HAR | exact Hr | lia].
- apply Z.ltb_ge in Hlt.
  assert (Hi' : i = sz / 8) by lia.
  apply orb_true_iff in Hlast as [H0|H0]; [apply Z.eqb_eq in H0; exfalso; lia|].
  apply existsb_exists in H0 as (c & Hc & Hcb). apply is_shv_eq in Hcb. subst c. subst i.
  unfold shadow_of_addr.
  etransitivity; [exact (grantB_shadow_cell ly S W mem md _ _ HAR Hc)|]. rewrite le_byte1 by lia. reflexivity.
Qed.

(* ---- 6. the image facts IMG_* --------------------------------------------------------------------------------------
   The byte facts are GrantBImgFacts.v's corollaries, each at `ro_free GrantB a n`, which is checked here against
   GrantB's owned statics and errno cell (ro_free_of_b). The place facts (alignment, bounds, in_zs, apartness) are
   computations on image B's listing and GrantB's zero-shadow ranges. *)
Lemma grantB_IMG_CTRL_ROW : GrantBContracts.IMG_CTRL_ROW (PI := PI_grant) GrantB.
Proof. unfold GrantBContracts.IMG_CTRL_ROW, GrantBContracts.B_ROW, IMG_LO, IMG_HI. zchk. Qed.

Lemma grantB_IMG_CTRL_ROW_FIN : GrantBContracts.IMG_CTRL_ROW_FIN (PI := PI_grant) GrantB.
Proof. apply GrantBImgFacts.img_ctrl_row_fin. rofree. Qed.

Lemma grantB_IMG_CTRL_LAY_JT : GrantBContracts.IMG_CTRL_LAY_JT (PI := PI_grant) GrantB.
Proof.
unfold GrantBContracts.IMG_CTRL_LAY_JT, IMG_LO, IMG_HI.
exists (nth 2 lay_jt_slots 0 + grant_text - grant_obj 26).
split; [zchk|]. split; [zchk|]. split; [zchk|]. split; [zchk|]. split; [zchk|].
intros H mem HR.
assert (E : pa_val (PAImg := PI_grant) (A_OBJ GrantBContracts.B_JT_LAY) + 4 * Z.of_nat GrantBContracts.LAY_TMPL_ENTRY
            = grant_obj 26 + 8) by (vm_compute; reflexivity).
rewrite E. apply garr8_val_mem.
apply (arodata_garr8_rom grantsegsB0 grant_relro_lo grant_relro_hi GrantB (grant_obj 26 + 8)
         (GrantBImgFacts.vbytes (nth 2 lay_jt_slots 0 + grant_text - grant_obj 26) 4) H mem).
- exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 GrantBImgFacts.b_rom_checks)))))).
- unfold GrantBImgFacts.vbytes. rewrite length_map, length_seq. rofree.
- exact HR.
Qed.

Lemma grantB_IMG_CTRL_STAMP_TM : exists TM, GrantBContracts.tmpl_place (PI := PI_grant) GrantB TM /\
  GrantBContracts.IMG_CTRL_ROW_LAY (PI := PI_grant) GrantB TM /\ GrantBContracts.IMG_CTRL_TMPL (PI := PI_grant) GrantB TM.
Proof.
exists 0x211c0. split; [|split].
- unfold GrantBContracts.tmpl_place, GrantBContracts.B_ROW, IMG_LO, IMG_HI.
  split; [zchk|]. split; [zchk|]. split; [zchk|]. split; [zchk|]. split; [zchk|].
  intros a Ha. apply grantB_in_img_seg0. lia.
- apply GrantBImgFacts.img_ctrl_row_lay. rofree.
- unfold GrantBContracts.IMG_CTRL_TMPL, GrantBContracts.B_ROW, IMG_LO, IMG_HI.
  split; [zchk|]. split; [zchk|]. split; [zchk|]. split; [zchk|]. split; [zchk|].
  apply GrantBImgFacts.img_ctrl_tmpl_bytes. rofree.
Qed.

Lemma grantB_IMG_BGS_ROWS : GrantBContracts.IMG_BGS_ROWS (PI := PI_grant) GrantB.
Proof. apply GrantBImgFacts.img_bgs_rows; rofree. Qed.

Lemma grantB_IMG_reac_ctrl_parse : GrantBContracts.IMG_reac_ctrl_parse (PI := PI_grant) GrantB.
Proof. apply GrantBImgFacts.img_reac_ctrl_parse. rofree. Qed.

Lemma grantB_IMG_check_groupa : GrantBContracts.IMG_check_groupa (PI := PI_grant) GrantB.
Proof. apply GrantBImgFacts.img_check_groupa. rofree. Qed.

Lemma grantB_IMG_LLVMF_SWEEP : GrantBContracts.IMG_LLVMF_SWEEP (PI := PI_grant) GrantB.
Proof. apply GrantBImgFacts.img_llvmf_sweep; rofree. Qed.

Lemma grantB_IMG_NEXT_DIV3 : GrantBContracts.IMG_NEXT_DIV3 (PI := PI_grant) GrantB.
Proof. apply GrantBImgFacts.img_next_div3. rofree. Qed.
End b.

(* ---- 7. the three facts of the record that GrantBTraces.img_llvmf_traces_grant reads ------------------------------- *)
(* H_universe_B: GrantB's trace universe is image B's (lib/B/YD2l.v:39). *)
Lemma grantB_universe : as_universe GrantB = YCej.Tfib_universe.
Proof. reflexivity. Qed.
(* H_malloc_ra0_B: the malloc interceptor's return address after its GetCurrentPc call (lib/B/YF0l.v:11). *)
Lemma grantB_malloc_ra0 : pc_malloc_ra0 (as_code GrantB) = 0x53178.
Proof. reflexivity. Qed.
(* H_free_ra0_B: the free interceptor's (lib/B/YF0l.v:12). *)
Lemma grantB_free_ra0 : pc_free_ra0 (as_code GrantB) = 0x53018.
Proof. reflexivity. Qed.
