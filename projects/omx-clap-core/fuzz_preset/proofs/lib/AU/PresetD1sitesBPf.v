(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the proofs of the results stated in lib/AU/PresetD1sitesB.v (fuzz_preset,
   asan-ubsan image), ported from proofs/cgif/cgif_file_fuzzer/lib (here relocated as lib/Reusable) with cgif's AR
   replaced by ARcf at Hp = [], AR_laws by a8's AR_laws_ok_cf (YG0lawscf.v) and ml_free by a8's ml_free_cf
   (YG03dcf.v:428):
     acall_pre_cf_of_drv    from YD1i.v:39-53 acall_pre_of_drv (through a8's acall_pre_cf_intro, YGcfRoomPre.v);
     call_trace_drv         YD1i.v:54-60, unchanged;
     free_site_cf_B_holds / free_null_site_cf_B_holds    (room: the interface's NP with PCB.iface_room_np_tail /
                                                          iface_room_np_step as hypotheses) from YD1i.v:61-94;
     drv_not_owned_cf / ARcf_after_run                    from YD1y.v:76-87 / :102-134;
     est_frame_run_cf / so_state_run_cf / run_to_exit_cf  from YD27.v:118-135 / :258-308;
     exit_leaf_cf_B_holds                                 from YD27.v:671-699.
   The symbolic runs of the driver's exit path (jx_run and the XSTS facts of YD27.v / YD28.v) name no allocator
   invariant and are used as they are. Rule 24: no function is proved here (composition / driver layer of a port). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0d YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK00 YK0h YK14 YK1b YK15
YK0k YK18 YK0p YP0n YK0s YM02 YP0m YP09 YP02 YP0l YP0k YP06 YP01 YP08 YP03 YP0g YP0e YN3q YN3v YI04 YL0a YL09 YL02
YL04 YK04 YA0i YA0n YA0o YA0p YA0m YK09 YA0e YG00 YG01 YG0k YG0f YG0v YG0n YG0d YCe5.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB12 YF0l YB1h YB13 YF0m YD2j YD2i YD1t
YD20 YD1v YD1y YD2a YD26 YD24.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YD21 YD25 YD22 YD23 YD2h YD1w YD2f YD2b YD2g
YD1s YD2c YD2d YD29 YD1x YD28 YD27.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO05 YO09 YO06 YO01 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YGcfTok YGcfRoomPre YG03dcf YG0lawscf YGcfXs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YG0dH YGcfRehidePost YG0dcfR YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetD1sitesB.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PresetCfnB.
Module PCB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PresetCfnB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable B : asyms.
Variable NP : astate -> Prop.
(* The interface's two laws of the non-primary room (lib/AU/PresetCfnB.v Section rm, lane IfacePort; bodies
   from a Theorem Labs lane at room_live_cf), taken as hypotheses. Nothing about NP is proved here. *)
Hypothesis NPTAIL : PCB.iface_room_np_tail NP.
Hypothesis NPSTEP : PCB.iface_room_np_step NP.
Let NPFREE := proj2 NPSTEP.
(* drv_pre_cf's hull and read-only conjuncts in acall_pre_cf's forms at this Section's cp / ci (PresetD1sitesB.v
   section 1); the closed results take them as premises. *)
Hypothesis HLINK : drv_hull_link.
Hypothesis ALINK : drv_aro_link B.

(* a8's one-call room premise from the interface's room: ROOM_cf_k S 2 is ROOM_cf S with slack. *)
Lemma ROOM_cf_of_NP : forall S, NP S -> ROOM_cf S.
Proof.
intros S H. pose proof (NPTAIL S H) as (R1 & R2 & R3).
unfold YGcfRoomKeep.ERRB_ROOM_k in R2. cbn [Z.of_nat] in R1, R2, R3.
unfold ROOM_cf, ERRB_ROOM, batch_room_cf. unfold kUserMapSize in *.
split; [lia|]. split; [lia | lia].
Qed.

(* ---------------------------------------------------------------------- *)
(* 1. The driver's call pre gives acall_pre_cf. Donor: YD1i.v:39-60. The call reads no memnorm (field round 3
      part 3c), so the pre without it (drv_pre_nomn_cf) gives it, and drv_pre_cf gives that pre. *)
Lemma layout_of_ARcf : forall ly S Hp (W : world tfibsegs) mem md, ARcf tfibsegs B ly S Hp W mem md -> layout_ok ly.
Proof. intros ly S Hp W mem md (HM & _). apply amc_layout in HM. exact HM. Qed.

Lemma drv_pre_nomn_of_drv : forall ly S W regs mem md,
drv_pre_cf B NP ly S W regs mem md -> drv_pre_nomn_cf B NP ly S W regs mem md.
Proof.
intros ly S W regs mem md (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & _ & H17).
exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11
  (conj H12 (conj H13 (conj H14 (conj H15 H17))))))))))))))).
Qed.

Lemma acall_pre_cf_of_drv_nomn : forall ly S W regs mem md,
drv_pre_nomn_cf B NP ly S W regs mem md -> acall_pre_cf tfibsegs B ly S [] W regs mem md [].
Proof.
intros ly S W regs mem md (HAR & [Elo Ehi] & Hret & Hra & Hal & [Wlo Whi] & [Tlo Thi] & Hpres & Hgp & Htp & Hs0 & Hqt & HNP & _ & HHO & HRO).
pose proof (ROOM_cf_of_NP S HNP) as HRM.
pose proof (layout_of_ARcf _ _ _ _ _ _ HAR) as LO. pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & _).
unfold ly_bot in *. unfold sp_window_lo, sp_window_hi in *.
apply acall_pre_cf_intro; [exact HAR | exact Hqt | exact HRM | exact (HLINK S HHO) | exact (ALINK W mem HRO) |
  exact Hret | exact Hal | | | | exact Hpres | exact Hgp | exact Htp |].
- unfold ly_bot, kStackSpan, ASTACK in *; lia.
- unfold ly_bot, kStackSpan in *; lia.
- rewrite Ehi; unfold kHighMemEnd; lia.
- unfold chain_pre. split; [exact Hra|].
destruct (frame0_ok ly regs); [| reflexivity].
replace (bad_next (spZ regs) (ly_top ly) (s0Z regs)) with true; [reflexivity|].
symmetry. unfold bad_next. apply Bool.orb_true_intro. left. apply Bool.orb_true_intro. left. apply Z.leb_le.
pose proof (lo_stk_ceil _ LO) as SC. unfold ASAN_CEIL in SC. unfold kStackSpan in *. lia.
Qed.

Lemma acall_pre_cf_of_drv : forall ly S W regs mem md,
drv_pre_cf B NP ly S W regs mem md -> acall_pre_cf tfibsegs B ly S [] W regs mem md [].
Proof.
intros ly S W regs mem md H. exact (acall_pre_cf_of_drv_nomn ly S W regs mem md (drv_pre_nomn_of_drv ly S W regs mem md H)).
Qed.

Lemma call_trace_drv : forall ly regs pc0, call_trace ly pc0 regs [] = [pc0; raZ regs] \/ call_trace ly pc0 regs [] = [pc0].
Proof.
intros ly regs pc0. unfold call_trace. destruct (frame0_ok ly regs); [| right; reflexivity].
unfold unwind_of_chain. cbn [flat_map app]. destruct (raZ regs =? pc0) eqn:E.
- right. reflexivity.
- left. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. The free sites. A free pays NO headroom: its one-call ROOM_cf comes from NP by iface_room_np_tail, and
      the post's NP S' from the FREE ARM of a8's iface_room_np_step (NPFREE below), with the driver's live
      bound `length (blocks S) <= 3` and the Wf_cf / qtight that a driver state already carries.
      Donor: YD1i.v:61-94. The row is the primed free contract (YG0dcfR.afree_realizes_cf_rh, amreal' over RZ_cf),
      in its keep form where the site's post carries the memnorm keep: amreal'_SRr' (YG0dH) gives the SRr' fact,
      and the leaf's acall_post_cf_rh is the site's post at the site's exception set. The sites over drv_pre_nomn_cf
      are proved; those over drv_pre_cf follow by drv_pre_nomn_of_drv (the posts are the same). *)
Lemma free_site_nomn_cf_sec : YGcfMallocComposeKeep.afree_realizes_cf_rh_keep tfibsegs B -> free_site_nomn_cf B NP.
Proof.
intros AFREE ly S W regs mem md p n HPRE HLIVE Hin Ha0 Htr2 Htr1.
pose proof (acall_pre_cf_of_drv_nomn _ _ _ _ _ _ HPRE) as HAP.
pose proof HPRE as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hqt & HNP & HXS & _).
pose proof (ROOM_cf_of_NP S HNP) as HRM.
pose proof (proj1 HAR) as HWF. apply amc_wf in HWF. pose proof (proj1 HAR) as HU. apply amc_universe in HU.
assert (Htr : In (call_trace ly (pc_free_ra0 (as_code B)) regs []) (as_universe B)).
{ destruct (call_trace_drv ly regs (pc_free_ra0 (as_code B))) as [-> | ->]; assumption. }
pose proof (ml_free_cf (as_universe B) HU S p n (call_trace ly (pc_free_ra0 (as_code B)) regs []) HWF (proj2 (proj2 HRM)) (or_intror Hin) (YG01.admits_fix _ _ S HU Htr)) as HTOK.
pose proof (AFREE ly S [] W regs mem md p n [] HAP (or_intror Hin) Ha0 (fun X => X) (YG01.admits_fix _ _ S HU Htr)) as HREAL.
unfold YA0nH.SRr'.
eapply YA0nH.SRrG_mono; [exact (YG0dH.amreal'_SRr' tfibsegs YGcfRehidePost.RZ_cf _ W _ _ HREAL (atok_cf_asafe _ _ _ HTOK) (atok_cf_agprog _ _ _ HTOK) (atok_cf_nospin _ _ HTOK))|].
cbv beta. intros W' c' _ ([[] S'] & tr & Hpath & (HL & HMNK)).
destruct HL as (ly' & regs' & mem' & md' & Hc & HPOST & HQT & _ & _). subst c'. cbn [snd] in HPOST, HQT.
exists ly', S', regs', mem', md', (call_trace ly (pc_free_ra0 (as_code B)) regs []), tr.
split; [exact Htr|]. split; [exact Hpath|]. split; [reflexivity|].
pose proof HPOST as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
split; [| split; [exact HQT | split; [exact (NPFREE (as_universe B) S p (call_trace ly (pc_free_ra0 (as_code B)) regs []) tr S' HWF Hqt HNP HLIVE Hpath) |
  split; [| exact (HMNK (raZ regs) regs' mem' md' eq_refl)]]]].
2:{ pose proof HWF as W0. unfold Wf_cf in W0. destruct (free_cf_frame _ _ _ _ _ Hpath) as [FX FS].
apply (xs_placed_cf_mono ly' S S' (FX ly')); [intros z Hz; left; exact (FS ly' z Hz) |].
exact (xs_placed_cf_layout _ _ _ _ ly ly' S W0 P2 HXS). }
split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [| exact P7].
intros a Ha Ho Ho' Hs HE HD. apply P6; [exact Ha | exact Ho | exact Ho' | exact Hs | | exact HD]. intros [_ X]. exact (HE X).
Qed.

Lemma free_null_site_nomn_cf_sec : YG0dcfR.afree_realizes_cf_rh tfibsegs B -> free_null_site_nomn_cf B NP.
Proof.
intros AFREE ly S W regs mem md HPRE HLIVE Ha0 Htr2 Htr1.
pose proof (acall_pre_cf_of_drv_nomn _ _ _ _ _ _ HPRE) as HAP.
pose proof HPRE as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hqt & HNP & HXS & _).
pose proof (ROOM_cf_of_NP S HNP) as HRM.
pose proof (proj1 HAR) as HWF. apply amc_wf in HWF. pose proof (proj1 HAR) as HU. apply amc_universe in HU.
assert (Htr : In (call_trace ly (pc_free_ra0 (as_code B)) regs []) (as_universe B)).
{ destruct (call_trace_drv ly regs (pc_free_ra0 (as_code B))) as [-> | ->]; assumption. }
pose proof (ml_free_cf (as_universe B) HU S PNull 0 (call_trace ly (pc_free_ra0 (as_code B)) regs []) HWF (proj2 (proj2 HRM)) (or_introl eq_refl) (YG01.admits_fix _ _ S HU Htr)) as HTOK.
pose proof (AFREE ly S [] W regs mem md PNull 0 [] HAP (or_introl eq_refl) Ha0 (fun X => X) (YG01.admits_fix _ _ S HU Htr)) as HREAL.
unfold YA0nH.SRr'.
eapply YA0nH.SRrG_mono; [exact (YG0dH.amreal'_SRr' tfibsegs YGcfRehidePost.RZ_cf _ W _ _ HREAL (atok_cf_asafe _ _ _ HTOK) (atok_cf_agprog _ _ _ HTOK) (atok_cf_nospin _ _ HTOK))|].
cbv beta. intros W' c' _ ([[] S'] & tr & Hpath & (ly' & regs' & mem' & md' & Hc & HPOST & HQT & _ & _)).
subst c'. cbn [snd] in HPOST, HQT.
exists ly', S', regs', mem', md', (call_trace ly (pc_free_ra0 (as_code B)) regs []), tr.
split; [exact Htr|]. split; [exact Hpath|]. split; [reflexivity|].
pose proof HPOST as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
split; [| split; [exact HQT | split; [exact (NPFREE (as_universe B) S PNull (call_trace ly (pc_free_ra0 (as_code B)) regs []) tr S' HWF Hqt HNP HLIVE Hpath) |]]].
2:{ pose proof HWF as W0. unfold Wf_cf in W0. destruct (free_cf_frame _ _ _ _ _ Hpath) as [FX FS].
apply (xs_placed_cf_mono ly' S S' (FX ly')); [intros z Hz; left; exact (FS ly' z Hz) |].
exact (xs_placed_cf_layout _ _ _ _ ly ly' S W0 P2 HXS). }
split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [| exact P7].
intros a Ha Ho Ho' Hs _ HD. apply P6; [exact Ha | exact Ho | exact Ho' | exact Hs | | exact HD]. intros [X _]. exact (X eq_refl).
Qed.

Lemma free_site_cf_sec : YGcfMallocComposeKeep.afree_realizes_cf_rh_keep tfibsegs B -> free_site_cf B NP.
Proof.
intros AFREE ly S W regs mem md p n HPRE.
exact (free_site_nomn_cf_sec AFREE ly S W regs mem md p n (drv_pre_nomn_of_drv ly S W regs mem md HPRE)).
Qed.

Lemma free_null_site_cf_sec : YG0dcfR.afree_realizes_cf_rh tfibsegs B -> free_null_site_cf B NP.
Proof.
intros AFREE ly S W regs mem md HPRE.
exact (free_null_site_nomn_cf_sec AFREE ly S W regs mem md (drv_pre_nomn_of_drv ly S W regs mem md HPRE)).
Qed.

(* ---------------------------------------------------------------------- *)
(* 3. ARcf across a driver run that writes only its stack window and the driver's image cells. Local: CwLoopB's
      lib/A/PresetD1rAx.v (lib/AU/PresetD1rBx.v) owns drv_not_owned_cf / AR_after_run_cf for the port; these copies go
      when it lands.
      Donor: YD1y.v:76-87 (drv_not_owned) and :102-134 (AR_after_run). *)
Section R.
Hypothesis HB : TfibSyms B.
Let ARL : AR_laws_cf tfibsegs B := AR_laws_ok_cf tfibsegs B.

Local Lemma drv_not_owned_cf : forall ly S Hp W mem md a sp0,
ARcf tfibsegs B ly S Hp W mem md -> sp_window_lo <= sp0 -> YM05.ceil_of_top (sp0 - stack_max_size) ->
(sp0 - 65536 <= a < sp0) \/ DRVW a = true -> ~ aowned B ly S a.
Proof.
intros ly S Hp W mem md a sp0 HAR Hsp HCT Ha Ho.
destruct Ha as [Ha|Ha].
- pose proof (alc_owned_low _ _ ARL ly S Hp W mem md a HAR Ho) as L. pose proof (YM05.ceil_le_top _ HCT) as LT.
unfold sp_window_lo, stack_max_size in *. lia.
- pose proof (DRVW_rw a Ha) as R.
apply (DRVW_not_owned a Ha). rewrite <- (ts_owned B HB).
exact (proj1 (alc_owned_image _ _ ARL ly S Hp W mem md a HAR (in_img_rw a R)) Ho).
Qed.

Local Lemma ARcf_after_run : forall ly S Hp W E rs (mem mem' : word -> option byte) md mat,
ARcf tfibsegs B ly S Hp W mem md ->
forallb drv_win_ok rs = true -> sp_window_lo <= bv_unsigned (ew E 0) -> YM05.ceil_of_top (bv_unsigned (ew E 0) - stack_max_size) ->
frame_of E rs mem mem' ->
(forall a, bv_unsigned (ew E 0) - 65536 <= a < bv_unsigned (ew E 0) -> mem' (Z_to_bv 64 a) <> None) ->
ARcf tfibsegs B ly S Hp W mem' (with_vm_backing (m_vm_lazy md) mat md).
Proof.
intros ly S Hp W E rs mem mem' md mat HAR Hok Hsp HCT HF Hpres.
apply (alc_frame _ _ ARL ly S Hp W mem md mem' (with_vm_backing (m_vm_lazy md) mat md) HAR).
- intros a Ha Ho. unfold aview, mbyte, mrestrict.
assert (Hx : mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ apply HF. intros Hw. apply (drv_not_owned_cf ly S Hp W mem md a (bv_unsigned (ew E 0)) HAR Hsp HCT); [|exact Ho].
rewrite u64_lit in Hw by lia. exact (in_wrange_drv E rs a Hok Hw). }
rewrite Hx. reflexivity.
- intros a Hv. unfold aview, mbyte, mrestrict in *. destruct (w_H W (Z_to_bv 64 a)) eqn:Hh; [exact Hv|].
destruct (mem' (Z_to_bv 64 a)) as [b'|] eqn:Em'; [cbn; discriminate|].
destruct (in_wrangeb E rs (bv_unsigned (Z_to_bv 64 a))) eqn:Hw.
+ apply in_wrangeb_true in Hw. destruct (in_wrange_drv E rs _ Hok Hw) as [Hs|Hd].
* exfalso. pose proof (Hpres (bv_unsigned (Z_to_bv 64 a)) Hs) as P. rewrite Z_to_bv_bv_unsigned in P. exact (P Em').
* destruct (seg_rom tfibsegs (Z_to_bv 64 a)) as [b|] eqn:Es; [cbn; discriminate|].
exfalso. pose proof (tfib_rw_rom (bv_unsigned (Z_to_bv 64 a)) (DRVW_rw _ Hd)) as R. rewrite Z_to_bv_bv_unsigned in R. exact (R Es).
+ apply in_wrangeb_false in Hw. rewrite (HF _ Hw) in Em'. rewrite Em' in Hv. exact Hv.
- reflexivity.
- rewrite m_vm_lazy_wvb. reflexivity.
- unfold eager_used. rewrite m_vm_lazy_wvb. reflexivity.
-
intros a Ha _. apply (HF (w64 a)). intros Hw. unfold w64 in Hw.
unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha.
rewrite u64_lit in Hw by lia.
destruct (in_wrange_drv E rs a Hok Hw) as [Hs|Hd].
+ clear - Ha Hs Hsp. unfold sp_window_lo, stack_max_size in *. lia.
+ pose proof (DRVW_rw a Hd) as X. clear - Ha X. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* 4. The exit leaf. Donor: YD27.v:99-135 (Section f), :258-308 (run_to_exit), :671-699 (tfib_exit_leaf). *)
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Variable est : (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis XFR : xst_frame_tfa xst.
Hypothesis ESTI : est_img_tfa est.
Hypothesis ESTF : est_frame_tfa est.
Hypothesis EXS : exit_site_cf B est xst.

Lemma est_frame_run_cf : forall H E rs m m',
frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb se_win_ok rs = true -> sp_window_lo <= bv_unsigned (ew E 0) ->
est H m -> est H m'.
Proof.
intros H E rs m m' HF Hok U0 HE. apply (ESTF H H m m' HE). intros a Ha.
apply (aview_kept_run F_STDERR_LO F_STDERR_HI E rs H m m' a HF Hok U0); unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI in *; lia.
Qed.

Lemma so_state_run_cf : forall k H E rs m m',
frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb sx_win_ok rs = true -> sp_window_lo <= bv_unsigned (ew E 0) ->
so_state xst k H m -> so_state xst k H m'.
Proof.
intros k H E rs m m' HF Hok U0 HS. apply (so_state_keep xst XFR k H H m m'); [| exact HS]. intros a Ha.
assert (H1 : forallb (win_avoids STDOUT_LO STDOUT_HI) rs = true /\ forallb (win_avoids SOBUF_LO SOBUF_HI) rs = true).
{ split; apply forallb_forall; intros r Hr; pose proof (proj1 (forallb_forall _ _) Hok r Hr) as X; unfold sx_win_ok in X; apply andb_prop in X; tauto. }
destruct Ha as [Ha|Ha].
- apply (aview_kept_run STDOUT_LO STDOUT_HI E rs H m m' a HF (proj1 H1) U0); unfold STDOUT_LO, STDOUT_HI in *; lia.
- apply (aview_kept_run SOBUF_LO SOBUF_HI E rs H m m' a HF (proj2 H1) U0); unfold SOBUF_LO, SOBUF_HI in *; lia.
Qed.

Lemma run_to_exit_cf : forall (i : nat) ss0 E (W : world tfibsegs) ms md ly S (usp : Z) fs (code : Z) (k : nat) (I0 : smem) spo0 wf0,
(i < 5)%nat ->
SRr tfibsegs W (mkCfg ms md) (at_rs (ss_mem ss0) (nth i XSTS S_J7x) E W (ms_mem ms) md) ->
ss_mem ss0 = jmemI I0 spo0 wf0 -> XIok I0 -> (spo0 = -128 \/ spo0 = -48) -> (i = 2%nat \/ k = 0%nat) ->
bv_unsigned (ew E 0) = usp -> sp_window_lo <= usp <= sp_window_hi -> usp mod 16 = 0 -> 1 <= bv_unsigned (ew E 8) <= 4194303 ->
sv_denot E (nth i X_a0 (SLit 0)) = w64 code -> (code = 0 \/ code = 2) ->
AI tfibsegs (w_H W) (w_A W) md -> ARcf tfibsegs B ly S [] W (ms_mem ms) md -> top_ok usp ly ->
est (w_H W) (ms_mem ms) -> so_state xst k (w_H W) (ms_mem ms) ->
((1 <= k)%nat -> fd_lookup (m_fds md) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) -> m_fs md = fs ->
srealizes tfibsegs (mkCfg ms md) (wr ch_stdout (concat (repeat line0 (k - 1))) (ex code fs)).
Proof.
intros i ss0 E W ms md ly S usp fs code k I0 spo0 wf0 Hi HRUN Hm0 HI0 Hspo0 Hik E0 [Ulo Uhi] U16 Htid Hcode Hc02 HAI HAR HTOP HE HSO Hfd1 Hfs.
pose proof (u64_range (ew E 0)) as U0.
set (ssx := nth i XSTS S_J7x) in *.
pose proof (proj1 (Forall_forall _ _) XSTS_facts ssx ltac:(subst ssx; apply nth_In; cbn; lia)) as (Hpc & G3 & G4 & Hrv & _).
pose proof (XSTS_row i Hi) as (Ra0 & Rsp & Rra & Mx & Hret & Hspo & Hmspo & HXI & HXlate). fold ssx in Ra0, Rsp, Rra, Mx.
set (spo := nth i X_spo 0) in *. set (rav := nth i X_ra 0) in *. set (mspo := nth i X_mspo 0) in *. set (wf := nth i X_wf false) in *. set (XI := nth i X_img IMG_X) in *.
pose proof (jmemI_checks I0 spo0 wf0 HI0 Hspo0) as (WOK0 & SEK0 & SXK0 & _). pose proof (jmemI_checks XI mspo wf HXI Hmspo) as (WOK & SEK & SXK & JWF & _).
apply (SRr_srealizes tfibsegs W (mkCfg ms md) _ _ HRUN HAI).
intros W1 c1 _ HAI1 (-> & msX & matX & -> & HSX & HFX & HFrX). cbn [cfg_model] in HAI1. rewrite Hm0 in HFX, HFrX.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E ssx msX HSX Hrv) as Hshape.
pose proof (st_ok_mem_ok tfibsegs E ssx _ HSX) as HMX. cbn [restrict ms_mem] in HMX. rewrite Mx in HMX.
pose proof (jmemI_present XI mspo wf E (w_H W) (ms_mem msX) usp HMX E0 (conj Ulo Uhi) Hmspo) as HwinX.
assert (RG : forall r, getr (ms_regs msX) r = sv_denot E (sr_get (ss_regs ssx) r)) by (intros r; exact (st_ok_restrict_reg tfibsegs (w_H W) E ssx msX r HSX)).
rewrite Hshape, Hpc. change (Z_to_bv 64 A_exit) with (w64 A_exit).
apply (EXS XI E W (ms_regs msX) (ms_mem msX) (with_vm_backing (m_vm_lazy md) matX md) ly S usp (- spo) fs code k).
-
destruct HXlate as [[HL _] | [HX Hne]]; [right; exact HL | left]. split; [exact HX|]. destruct Hik as [Hik | Hk]; [exfalso; exact (Hne Hik) | exact Hk].
- exact E0.
- lia.
- exact U16.
- exact Htid.
- rewrite (RG 10%bv), Ra0. exact Hcode.
- exact Hc02.
- unfold spZ. rewrite (RG 2%bv), Rsp. cbn [sv_denot]. rewrite E0, u64_lit by (unfold sp_window_lo in Ulo; lia). lia.
- lia.
- rewrite (RG 1%bv), Rra. cbn [sv_denot]. exact Hret.
- rewrite (RG 3%bv), G3. reflexivity.
- rewrite (RG 4%bv), G4. reflexivity.
- apply (mem_ok_sub tfibsegs E _ (jmemI XI mspo wf)); [unfold jmemI; do 2 apply submem_drop; apply submem_refl | exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (XI_checks XI HXI))))))) | exact HMX].
- exact HwinX.
- exact HAI1.
- apply (ARcf_after_run ly S [] W E (jmemI I0 spo0 wf0) (ms_mem ms) (ms_mem msX) md matX HAR WOK0); [rewrite E0; exact Ulo | rewrite E0; exact (top_ok_ceil _ _ HTOP) | exact HFX |].
rewrite E0. intros a Ha. exact (apresent_some' _ _ _ (HwinX a Ha)).
- exact HTOP.
- exact (est_frame_run_cf (w_H W) E (jmemI I0 spo0 wf0) _ _ HFrX SEK0 ltac:(rewrite E0; exact Ulo) HE).
- exact (so_state_run_cf k (w_H W) E (jmemI I0 spo0 wf0) _ _ HFrX SXK0 ltac:(rewrite E0; exact Ulo) HSO).
- intros Hk. rewrite wvb_fds'. exact (Hfd1 Hk).
- rewrite wvb_fs'. exact Hfs.
Qed.

Lemma exit_leaf_cf_sec : exit_leaf_cf B xst.
Proof.
intros E W regs mem md ly S usp fs code k E0 [Ulo Uhi] U16 Htid Ra0 Hc02 Hsp R3 R4 HM Hwin HAI HAR HTOP HSO Hfds Hfs.
pose proof (ESTI (w_H W) mem (stderr_of_L E (w_H W) mem HM)) as HE.
pose proof (regs_ok_J E regs (-48) usp E0 ltac:(lia) Ulo ltac:(lia) R3 R4) as HR.
pose proof (st_ok_J IMG_XL E regs (jregs (-48)) (-48) YD1w.A_EXIT usp false (w_H W) mem (or_intror eq_refl) HR E0 Ulo ltac:(right; split; reflexivity) (mem_ok_XL_of_L E _ HM) Hwin ltac:(discriminate)) as HS.
unfold YD1w.A_EXIT in HS. rewrite <- (proj1 (proj2 (proj2 S_J_defs))), <- restrict_mkst_fx in HS.
fold YD1w.A_EXIT in HS. change (Z_to_bv 64 YD1w.A_EXIT) with (w64 YD1w.A_EXIT) in HS.
set (E2 := E_J E regs) in *.
assert (E2_0 : bv_unsigned (ew E2 0) = usp) by (subst E2; rewrite E_J_old by (unfold KJ; lia); exact E0).
pose proof S_JFc_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MX).
apply (run_to_exit_cf 2%nat S_JX E2 W _ md ly S usp fs code k IMG_XL (-48) false ltac:(lia)); [| | right; reflexivity | | left; reflexivity | ..].
- cbn [nth XSTS]. rewrite MX. exact (jx_run E2 W _ md HS).
- exact MX.
- right. reflexivity.
- exact E2_0.
- exact (conj Ulo Uhi).
- exact U16.
- subst E2. rewrite E_J_old by (unfold KJ; lia). exact Htid.
- cbn [nth X_a0 sv_denot]. rewrite Z.add_0_r. subst E2. change 206%nat with (KJ + 6)%nat. rewrite (E_J_new E regs 6 10%bv) by (first [cbn; lia | reflexivity]). rewrite Z_to_bv_bv_unsigned. exact Ra0.
- exact Hc02.
- exact HAI.
- exact HAR.
- exact HTOP.
- exact HE.
- exact HSO.
- intros Hk. rewrite Hfds. reflexivity.
- exact Hfs.
Qed.
End R.
End P.

(* ---------------------------------------------------------------------- *)
(* 5. The closed results. *)
Theorem free_site_cf_B_holds : free_site_cf_B.
Proof. intros fx rc ci cp B NP HTAIL HSTEP HL AL AFREE. exact (free_site_cf_sec B NP HTAIL HSTEP HL AL AFREE). Qed.

Theorem free_null_site_cf_B_holds : free_null_site_cf_B.
Proof. intros fx rc ci cp B NP HTAIL HSTEP HL AL AFREE. exact (free_null_site_cf_sec B NP HTAIL HSTEP HL AL AFREE). Qed.

Theorem free_site_nomn_cf_B_holds : free_site_nomn_cf_B.
Proof. intros fx rc ci cp B NP HTAIL HSTEP HL AL AFREE. exact (free_site_nomn_cf_sec B NP HTAIL HSTEP HL AL AFREE). Qed.

Theorem free_null_site_nomn_cf_B_holds : free_null_site_nomn_cf_B.
Proof. intros fx rc ci cp B NP HTAIL HSTEP HL AL AFREE. exact (free_null_site_nomn_cf_sec B NP HTAIL HSTEP HL AL AFREE). Qed.

Theorem exit_leaf_cf_B_holds : exit_leaf_cf_B.
Proof.
intros fx rc ci cp B xst est HB XFR ESTI ESTF EXS.
exact (exit_leaf_cf_sec B HB xst est XFR ESTI ESTF EXS).
Qed.

Print Assumptions free_site_cf_B_holds.
Print Assumptions free_site_nomn_cf_B_holds.
