(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the parts the walk of plugin-hostd/fuzz_command's strdup entry needs that no file of this tree holds: the code table of the entry (the shape of lib/A/AE34.v), the two phase lemmas (the shape of lib/A/AE2y.v icpt_phase), and one lemma that carries an [amreal] post through a later run. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Rt/RtDStrdupD.v, with its module names changed; 246 of its 279 lines of code are new or changed and 54 lines of the source are left out. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0j YFfk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB1v YE34 YF0l YF0m YF0x YB1w YE20 YE2y YCeg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YO0d.
(* YO0d has its own spZ and raZ; the contracts use YG0d's *)
Import YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtAlloc RtDDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDStrndupL RtDStrndupP RtDStrndupA RtDStrndupF RtDStrndupR.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The contract of plugin-hostd/fuzz_command's strndup interceptor on its ASan+UBSan image (fuzz_command.asan-ubsan;
   the proof of lib/A/Rt/RtDStrndup.v moved by the name-keyed A-to-B address map) (RtAlloc.v:100 astrndup_realizes at the trampoline
   PC_strndup 0x45184, unwinder pc PC_STRNDUP_RA0 0x58c6c, malloc return PC_STRNDUP_MID 0x457bc), composed from:
     RtDStrndupA.v snd_pre      the trampoline to the call of the malloc body (internal_strnlen included)
     RtDDefs.v amalloc_body_realizes at 0x58ba4 (the Section hypothesis AMALLOC_BODY below), whose trace is the
                                contract's adup_trace (RtDStrndupA.v snd_trace_eq)
     RtDStrndupR.v snd_post     the malloc body's return to the entry's own return
   The source lies in a live block of the allocator; it is the same live block after the allocation (the model's
   malloc_post, through YG05.model_laws_ok on the record's universe), so its bytes are kept by the body's frame and
   its shadow is the block's (AR_shadow_law at the state after the allocation). *)

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* an [amreal] post followed by a run of the real machine *)
Lemma amreal_then_SRr {R} : forall (t : itree astate R) (W : world tfibsegs) c
(P Q : R -> world tfibsegs -> config -> Prop),
amreal tfibsegs t W c P -> (forall r W' c', P r W' c' -> SRr tfibsegs W' c' (Q r)) ->
amreal tfibsegs t W c Q.
Proof.
induction t as [r | q s k IH | pc | f]; intros W c P Q H HK; cbn [amreal] in *.
- eapply SRr_bind; [exact H|]. intros W' c' _ HP. exact (HK r W' c' HP).
- eapply SRr_mono; [exact H|]. intros W1 c1 _ Hk. destruct q;
try (destruct Hk as (J & nx & bit & sp & i0 & Hn & Ht & Ha & Hs & Hb & Hr & Hz & Hc); exists J, nx, bit, sp, i0;
split; [exact Hn|]; split; [exact Ht|]; split; [exact Ha|]; split; [exact Hs|]; split; [exact Hb|]; split; [exact Hr|];
split; [exact Hz|]; intros i Hi; eapply IH; [apply Hc, Hi | exact HK]).
destruct Hk as (z & Hz & Hc). exists z. split; [exact Hz|]. eapply IH; [exact Hc | exact HK].
- exact H.
- exact I.
Qed.
End a.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : CmdBSyms B.
(* The malloc interceptor's body entered by a call, with strndup's unwinder pc: RtDDefs.v:72 (proved on this image by
   lib/B/Rt/RtDMallocBody.v cmd_amalloc_body, PC_STRNDUP_RA0 = DM_PC0 = 0x58c6c, under its own two hypotheses). *)
Hypothesis AMALLOC_BODY : amalloc_body_realizes tfibsegs B PC_malloc_body PC_STRNDUP_RA0.

Theorem cmd_strndup : astrndup_realizes tfibsegs B PC_strndup PC_STRNDUP_RA0 PC_STRNDUP_MID.
Proof.
intros ly S W regs mem md x n buf ch k HPRE G10 G11 Hn Hx Hbytes Hok Hread Hblk Herr HROM Hk1 Hlive Htr.
pose proof HPRE as (HAR & Hreg & Hra & Hal16 & Hslo & Hbot & Htop & HpresA & Hgp & Htp & Hch & Hqm).
pose proof (strnlen_res_facts x n buf ltac:(lia) Hok) as (K0 & Kl & _ & Kz).
change (PStrFun.strnlen_res n buf) with k in K0, Kl, Kz.
set (L := Z.min (k + 1) (Z.of_nat (length buf))) in *.
set (mm0 := RtDStrndupP.mm n k).
assert (MML : k <= mm0 <= L /\ mm0 <= n /\ mm0 <= k + 1).
{ unfold mm0, RtDStrndupP.mm, L. destruct (Z_lt_le_dec k n) as [Hlt|Hge]; [specialize (Kz Hlt); lia | lia]. }
destruct Hread as (Hx0 & HxL & HL32 & Hsrcv & Ham & Hra0 & Hhull0).
destruct Hblk as (p0 & m0 & Hin0 & Hp0x & HxLp).
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
pose proof (lo_stk_ceil ly HLY) as Lceil.
pose proof ASAN_CEIL_range as [CR1 CR2].
unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi. unfold ASTACK in Hslo, HpresA.
set (sp0 := spZ regs) in *.
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47) by lia.
assert (Hxh : x + L < 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; lia).
(* the old block, before the allocation *)
destruct (al_blocks _ _ LAWS ly S W mem md p0 m0 HAR Hin0) as (Pal0 & P40 & Pce0 & Papp0 & Pby0 & _ & Pm0).
pose proof (req_size_bounds m0 ltac:(lia)) as RQ0.
pose proof (req_size_bounds (k + 1) ltac:(lia)) as RQk.
assert (Hheap : x + L <= ly_stk_lo ly).
{ unfold in_app, kLowShadowBeg, kHighMemBeg in Papp0. lia. }
(* the trampoline to the malloc body *)
assert (HSRC : forall j, (j < length buf)%nat -> (j <= Z.to_nat (PStrFun.strnlen_res n buf))%nat ->
aview tfibsegs (w_H W) mem (x + Z.of_nat j) = Some (bv_unsigned (nth j buf NUL)) /\
~ (spZ regs - SN_WIN <= x + Z.of_nat j < spZ regs)).
{ intros j Hj Hjk. change (PStrFun.strnlen_res n buf) with k in Hjk. split.
- exact (Hbytes j Hj).
- destruct (Hsrcv (x + Z.of_nat j) ltac:(lia)) as [_ Hns]. unfold ascratch_stk, ASTACK in Hns. fold sp0 in Hns |- *. unfold SN_WIN. lia. }
apply (amreal_SRr_pre tfibsegs _ W (cfg_at tfibsegs PC_strndup regs mem md) _ _
(snd_pre B LAWS TB ly S W regs mem md x n buf ch HPRE G10 G11 Hn ltac:(lia) Hok HSRC)).
intros W' c' _ (-> & regs_c & mem_c & md_c & -> & HPW & C10 & C1 & C2 & C8 & C9 & C18 & C20 & C21 & CK & Hsbm & MEQ & PRES & SAVED).
assert (Hspc : spZ regs_c = spZ regs - STRNDUP_FRAME) by (unfold spZ at 1; rewrite C2; unfold w64; apply unsigned_lit_small; unfold SN_FRAME, STRNDUP_FRAME; fold sp0; lia).
assert (Hrac : raZ regs_c = PC_STRNDUP_MID) by (unfold raZ; rewrite C1; reflexivity).
pose proof (snd_trace_eq ly regs regs_c ch PC_STRNDUP_RA0 PC_STRNDUP_MID Hspc Hrac ltac:(unfold PC_STRNDUP_MID; lia)) as ETR.
(* the model step: the allocation keeps the old blocks *)
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
assert (HADM : tr_admit (as_universe B) S (adup_trace ly PC_STRNDUP_RA0 PC_STRNDUP_MID regs ch)).
{ destruct Htr as [Htr|Htr]; [left; exact Htr | right; split; [apply snd_trace_len | exact Htr]]. }
pose proof (ml_malloc_ns _ (YG05.model_laws_ok _ (ts_universe B TB)) S (k + 1) (adup_trace ly PC_STRNDUP_RA0 PC_STRNDUP_MID regs ch)
HWF (aregime_ok S Hreg) ltac:(lia) Hlive HADM) as HTOK.
pose proof (AMALLOC_BODY ly S W regs_c mem_c md_c (k + 1) (snd_ch ly regs ch) HPW C10 ltac:(lia) Hlive
ltac:(rewrite ETR; exact Htr)) as HM.
rewrite ETR in HM.
assert (HPP : forall tr r, apath (malloc (k + 1) (adup_trace ly PC_STRNDUP_RA0 PC_STRNDUP_MID regs ch) S) tr r -> gflag tr = true ->
exists ns, malloc_post (as_universe B) S (k + 1) ns r).
{ intros tr r Hp _. exists (last_flag true tr). exact (proj1 (atok_apath_flag _ true _ tr r HTOK Hp)). }
pose proof (amreal_apostg tfibsegs _ _ W _ _ HPP HM) as HM2.
change (cfg_at tfibsegs SN_BODY regs_c mem_c md_c) with (cfg_at tfibsegs PC_malloc_body regs_c mem_c md_c).
apply (amreal_then_SRr _ W _ _ _ HM2).
intros [pr S2] W2 c2 [(ns & HMP) HLEAF].
destruct HMP as (HWF2 & Hnev2 & Hsecs2 & Hfrs2 & Hbl & _).
destruct HLEAF as (ly' & regs' & mem' & md' & -> & HPOST & R10 & HQT2).
pose proof HPOST as (HAR2 & Hlyle & Hwle2 & PRc & Hio & Hfr & Hpr2).
cbn [fst snd] in *.
pose proof (proj1 HPW) as HARc.
destruct (al_layout _ _ LAWS ly S W mem_c md_c ly' HARc Hlyle) as (Eab & _ & Eown).
pose proof Hlyle as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
(* the blocks after the allocation *)
assert (EB2 : (pr = PNull /\ ablocks B ly' S2 = ablocks B ly S) \/
(pr <> PNull /\ ablocks B ly' S2 = ablocks B ly S ++ [(sptr_addr B ly' pr, k + 1)])).
{ unfold ablocks in *. destruct pr as [| | |] eqn:Epr.
- left. split; [reflexivity|]. simpl in Hbl. rewrite Hbl. exact Eab.
- right. split; [discriminate|]. simpl in Hbl. destruct Hbl as [Hbl _]. rewrite Hbl, map_app, Eab. reflexivity.
- right. split; [discriminate|]. simpl in Hbl. destruct Hbl as [Hbl _]. rewrite Hbl, map_app, Eab. reflexivity.
- right. split; [discriminate|]. simpl in Hbl. destruct Hbl as [Hbl _]. rewrite Hbl, map_app, Eab. reflexivity. }
assert (Hp0 : pr = PNull -> sptr_addr B ly' pr = 0) by (intros E; rewrite E; reflexivity).
set (p := sptr_addr B ly' pr) in *.
assert (Hin2 : In (p0, m0) (ablocks B ly' S2)) by (destruct EB2 as [[_ E]|[_ E]]; rewrite E; [exact Hin0 | apply in_or_app; left; exact Hin0]).
destruct (al_blocks _ _ LAWS ly' S2 W2 mem' md' p0 m0 HAR2 Hin2) as (_ & _ & _ & _ & Pby2 & PW2 & _).
destruct (al_shadow _ _ LAWS ly' S2 W2 mem' md' p0 m0 HAR2 Hin2) as (Hbs2 & Hhull2).
(* the new block *)
assert (NB : pr <> PNull -> 4096 <= p /\ p + k + 1 <= ly_stk_lo ly /\ (p + (k + 1) <= p0 \/ p0 + req_size m0 <= p) /\
(forall a, p <= a < p + k + 1 -> apresent (w_H W2) mem' a /\ ~ aowned B ly' S2 a)).
{ intros Hnn. destruct EB2 as [[Epr _]|[_ E]]; [exfalso; exact (Hnn Epr)|].
assert (HinN : In (p, k + 1) (ablocks B ly' S2)) by (rewrite E; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly' S2 W2 mem' md' p (k + 1) HAR2 HinN) as (_ & P4 & _ & Papp & Pby & _ & _).
assert (Hdj : zdisjoint (p0, req_size m0) (p, req_size (k + 1))).
{ rewrite E in PW2. rewrite map_app in PW2. apply (in_split_pairwise _ _ _ _ PW2).
- apply (in_map (fun b => (fst b, req_size (snd b))) _ _ Hin0).
- left. reflexivity. }
unfold zdisjoint in Hdj. cbn [fst snd] in Hdj.
split; [exact P4|]. split; [unfold in_app, kLowShadowBeg, kHighMemBeg in Papp; lia|].
split; [lia|]. intros a Ha. apply Pby. lia. }
assert (Hpn : p <> 0 -> pr <> PNull) by (intros H0 H1; apply H0, Hp0, H1).
(* the source bytes and every byte of the old block survive the allocation *)
assert (SRC : forall a, p0 <= a < p0 + req_size m0 -> ~ aerrno_cell B a ->
aview tfibsegs (w_H W2) mem' a = aview tfibsegs (w_H W) mem a).
{ intros a Ha Hne.
assert (Hb0 : 4096 <= p0 /\ p0 + req_size m0 <= ASAN_CEIL) by (unfold in_app, kLowShadowBeg, kHighMemBeg in Papp0; lia).
rewrite Hfr.
- apply aview_same. apply MEQ. rewrite unsigned_lit_small by lia. fold sp0. unfold SN_WIN. lia.
- lia.
- exact (proj2 (Pby0 a Ha)).
- exact (proj2 (Pby2 a Ha)).
- intros [Hs|He]; [rewrite Hspc in Hs; fold sp0 in Hs; unfold MALLOC_IN_STK, STRNDUP_FRAME in Hs; lia | exact (Hne He)].
- intros [Hnn Hin]. destruct (NB Hnn) as (_ & _ & D & _). lia. }
assert (SRCx : forall a, x <= a < x + L -> aview tfibsegs (w_H W2) mem' a = aview tfibsegs (w_H W) mem a).
{ intros a Ha. apply SRC; [lia|]. intros He. apply Herr. exists a. split; [exact Ha | exact He]. }
(* the registers at 0x457bc *)
assert (PR : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs' r = getr regs_c r).
{ intros r Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). apply PRc. exact Hr. }
(* the saved words *)
assert (SV : forall j rz off, nth_error SAVEDA j = Some (rz, off) ->
word_mem tfibsegs (mrestrict (w_H W2) mem') (sp0 + off) (bv_unsigned (getr regs (Z_to_bv 5 rz)))).
{ intros j rz off Hj. apply (proj1 (val_mem_word_mem tfibsegs _ _ _)).
assert (Hoff : -80 <= off <= -8) by (do 10 (destruct j as [|j]; [cbn in Hj; injection Hj as <- <-; lia|]); destruct j; discriminate).
apply (YE2y.val_mem_kept (w_H W) (w_H W2) mem_c mem' (sp0 + off) 8 _); [|exact (SAVED j rz off Hj)].
intros q Hq. rewrite Hfr; [reflexivity | lia | | | |].
- intros Ho. exact (al_stack _ _ LAWS ly S W mem_c md_c (sp0 + off + q) HARc ltac:(lia) Ho).
- intros Ho. apply (al_stack _ _ LAWS ly' S2 W2 mem' md' (sp0 + off + q) HAR2); [rewrite Eslo, Eshi; lia | exact Ho].
- intros [Hs|He]; [rewrite Hspc in Hs; fold sp0 in Hs; unfold MALLOC_IN_STK, STRNDUP_FRAME in Hs; lia|].
unfold aerrno_cell in He. rewrite (ts_errno B TB) in He. unfold TFIB_ERRNO in He. lia.
- intros [Hnn Hin]. destruct (NB Hnn) as (_ & D & _). lia. }
(* the walk from the malloc body's return *)
unfold raZ at 1. rewrite C1. unfold w64 at 1. rewrite unsigned_lit_small by (unfold SN_MID; lia).
eapply SRr_mono.
{ apply (snd_post B LAWS TB ly' S2 W2 regs' mem' md' x n k p sp0 buf (raZ regs)
(bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9)) (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19))
(bv_unsigned (getr regs 20)) (bv_unsigned (getr regs 21)) (bv_unsigned (getr regs 22)) (bv_unsigned (getr regs 23))
(bv_unsigned (getr regs 24)) HAR2).
- intros a Hrom Hown Hne.
assert (Himg : in_img tfibsegs a) by (destruct Hrom as (sg & Hs & _ & Hb); exists sg; split; [exact Hs | exact Hb]).
pose proof (tfib_img_range a Himg) as Har.
rewrite Hfr.
+ rewrite (aview_same (w_H W) mem mem_c) by (apply MEQ; rewrite unsigned_lit_small by lia; fold sp0; unfold SN_WIN; lia).
exact (HROM a Hrom Hown Hne).
+ lia.
+ intros Ho. apply Hown. exact (proj1 (al_owned_image _ _ LAWS ly S W mem_c md_c a HARc Himg) Ho).
+ intros Ho. apply Hown. exact (proj1 (al_owned_image _ _ LAWS ly' S2 W2 mem' md' a HAR2 Himg) Ho).
+ intros [Hs|He]; [rewrite Hspc in Hs; fold sp0 in Hs; unfold MALLOC_IN_STK, STRNDUP_FRAME in Hs; lia | exact (Hne He)].
+ intros [Hnn Hin]. destruct EB2 as [[Epr _]|[_ E]]; [exact (Hnn Epr)|].
apply (proj2 (al_client_img _ _ LAWS ly' S2 W2 mem' md' a HAR2 ltac:(left; exists p, (k + 1); split; [rewrite E; apply in_or_app; right; left; reflexivity | exact Hin]))).
exact Himg.
- exact Hsp.
- exact Hal16.
- rewrite Eslo. lia.
- rewrite Eshi. lia.
- intros a Ha. apply Hpr2. rewrite Hspc. unfold MALLOC_IN_STK, STRNDUP_FRAME. fold sp0. lia.
- exact R10.
- rewrite PR by acs. exact C9.
- rewrite PR by acs. exact C20.
- rewrite PR by acs. exact C21.
- rewrite PR by acs. exact C8.
- rewrite PR by acs. exact C18.
- rewrite PR by acs. exact C2.
- pose proof (SV 0%nat 1 (-8) eq_refl) as V. replace (sp0 + -8) with (sp0 - 8) in V by lia. exact V.
- pose proof (SV 1%nat 8 (-16) eq_refl) as V. replace (sp0 + -16) with (sp0 - 16) in V by lia. exact V.
- pose proof (SV 2%nat 9 (-24) eq_refl) as V. replace (sp0 + -24) with (sp0 - 24) in V by lia. exact V.
- pose proof (SV 3%nat 18 (-32) eq_refl) as V. replace (sp0 + -32) with (sp0 - 32) in V by lia. exact V.
- pose proof (SV 4%nat 19 (-40) eq_refl) as V. replace (sp0 + -40) with (sp0 - 40) in V by lia. exact V.
- pose proof (SV 5%nat 20 (-48) eq_refl) as V. replace (sp0 + -48) with (sp0 - 48) in V by lia. exact V.
- pose proof (SV 6%nat 21 (-56) eq_refl) as V. replace (sp0 + -56) with (sp0 - 56) in V by lia. exact V.
- pose proof (SV 7%nat 22 (-64) eq_refl) as V. replace (sp0 + -64) with (sp0 - 64) in V by lia. exact V.
- pose proof (SV 8%nat 23 (-72) eq_refl) as V. replace (sp0 + -72) with (sp0 - 72) in V by lia. exact V.
- pose proof (SV 9%nat 24 (-80) eq_refl) as V. replace (sp0 + -80) with (sp0 - 80) in V by lia. exact V.
- unfold raZ. rewrite Z_to_bv_bv_unsigned. exact Hra.
- lia.
- fold mm0. lia.
- lia.
- lia.
- lia.
- destruct (Z.eq_dec p 0) as [E|E]; [lia|]. destruct (NB (Hpn E)) as (P4 & P5 & _). lia.
- fold mm0. intros a Ha. rewrite SRCx by lia. destruct (Hsrcv a ltac:(lia)) as [Hv _]. exact Hv.
- fold mm0. exact (ra_of_block _ p0 (req_size m0) x mm0 Hbs2 ltac:(lia) Hp0x ltac:(lia)).
- fold mm0. intros Hm0. exact (hull_sub _ p0 (req_size m0) x mm0 ltac:(lia) Hp0x Hm0 ltac:(lia) Hhull2).
- fold mm0. unfold amem_range in Ham |- *. lia.
- intros j Hj. rewrite SRCx by lia. exact (Hbytes j ltac:(lia)).
- intros Hpz. destruct (NB (Hpn Hpz)) as (P4 & P5 & P6 & P7). split; [lia|]. split; [lia|].
split; [lia|]. exact P7. }
cbv beta. intros W3 c3 _ (-> & regs'' & mem'' & md'' & -> & HAR3 & Hio3 & E10 & E2 & E1 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & EK & Hfr3 & Hpr3 & Hby).
exists ly', regs'', mem'', md''.
cbn [fst snd]. fold p.
split; [reflexivity|].
split.
{ split; [exact HAR3|]. split; [exact Hlyle|]. split; [exact Hwle2|].
split.
{ intros r Hr. unfold acallee_saved in Hr.
assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/
r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]].
- replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite E2. unfold sp0, spZ. apply Z_to_bv_bv_unsigned.
- replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite (EK 3%bv) by (left; reflexivity).
rewrite PR by acs. apply CK. cbn. tauto.
- replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite (EK 4%bv) by (right; left; reflexivity).
rewrite PR by acs. apply CK. cbn. tauto.
- replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite E8. apply Z_to_bv_bv_unsigned.
- replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite E9. apply Z_to_bv_bv_unsigned.
- replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite E18. apply Z_to_bv_bv_unsigned.
- replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite E19. apply Z_to_bv_bv_unsigned.
- replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite E20. apply Z_to_bv_bv_unsigned.
- replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite E21. apply Z_to_bv_bv_unsigned.
- replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite E22. apply Z_to_bv_bv_unsigned.
- replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite E23. apply Z_to_bv_bv_unsigned.
- replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite E24. apply Z_to_bv_bv_unsigned.
- replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite (EK 25%bv) by (right; right; left; reflexivity).
rewrite PR by acs. apply CK. cbn. tauto.
- replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite (EK 26%bv) by (right; right; right; left; reflexivity).
rewrite PR by acs. apply CK. cbn. tauto.
- replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite (EK 27%bv) by (right; right; right; right; reflexivity).
rewrite PR by acs. apply CK. cbn. tauto. }
split; [exact (same_io_tr md md_c md'' (same_io_sbm _ _ Hsbm) (same_io_tr md_c md' md'' Hio Hio3))|].
split.
{ intros a Ha Hown Hown2 Hscr HE.
rewrite Hfr3; [| exact Ha | unfold ascratch in Hscr; unfold ASTACK in Hscr; fold sp0 in Hscr; lia |].
- rewrite Hfr; [| exact Ha | exact Hown | exact Hown2 | | exact HE].
+ apply aview_same. apply MEQ. rewrite unsigned_lit_small by lia. unfold ascratch, ASTACK in Hscr. fold sp0 in Hscr. unfold SN_WIN. lia.
+ unfold ascratch in Hscr |- *. rewrite Hspc. unfold MALLOC_IN_STK, STRNDUP_FRAME, ASTACK in *. fold sp0 in Hscr |- *. lia.
- intros [Hpz Hin]. apply HE. split; [exact (Hpn Hpz) | pose proof (req_size_bounds (k + 1) ltac:(lia)); lia]. }
intros a Ha. unfold ASTACK in Ha. fold sp0 in Ha. apply Hpr3.
destruct (Z_lt_le_dec a (sp0 - 16368)) as [L1|L1].
- apply apresent_of_aview_hi; [unfold YF0x.TFIB_IMG_END; lia|].
rewrite Hfr; [| lia | | | | ].
+ rewrite (aview_same (w_H W) mem mem_c) by (apply MEQ; rewrite unsigned_lit_small by lia; unfold SN_WIN; lia).
apply aview_some_of_apresent. apply HpresA. lia.
+ intros Ho. exact (al_stack _ _ LAWS ly S W mem_c md_c a HARc ltac:(lia) Ho).
+ intros Ho. apply (al_stack _ _ LAWS ly' S2 W2 mem' md' a HAR2); [rewrite Eslo, Eshi; lia | exact Ho].
+ intros [Hs|He]; [rewrite Hspc in Hs; fold sp0 in Hs; unfold MALLOC_IN_STK, STRNDUP_FRAME in Hs; lia|].
unfold aerrno_cell in He. rewrite (ts_errno B TB) in He. unfold TFIB_ERRNO in He. lia.
+ intros [Hnn Hin]. destruct (NB Hnn) as (_ & D & _). lia.
- destruct (Z_lt_le_dec a (sp0 - 2160)) as [L2|L2].
+ apply Hpr2. rewrite Hspc. unfold MALLOC_IN_STK, STRNDUP_FRAME. fold sp0. lia.
+ apply apresent_of_aview_hi; [unfold YF0x.TFIB_IMG_END; lia|].
rewrite Hfr; [| lia | | | | ].
* apply aview_some_of_apresent. apply PRES. fold sp0. unfold SN_WIN. lia.
* intros Ho. exact (al_stack _ _ LAWS ly S W mem_c md_c a HARc ltac:(lia) Ho).
* intros Ho. apply (al_stack _ _ LAWS ly' S2 W2 mem' md' a HAR2); [rewrite Eslo, Eshi; lia | exact Ho].
* intros [Hs|He]; [rewrite Hspc in Hs; fold sp0 in Hs; unfold MALLOC_IN_STK, STRNDUP_FRAME in Hs; lia|].
unfold aerrno_cell in He. rewrite (ts_errno B TB) in He. unfold TFIB_ERRNO in He. lia.
* intros [Hnn Hin]. destruct (NB Hnn) as (_ & D & _). lia. }
split; [exact E10|].
split; [exact HQT2|].
intros Hnn. destruct (NB Hnn) as (P4 & _). apply Hby. lia.
Qed.
End g.
