(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of ctrl_lay_block on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8k.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChz.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACa2.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACb8.v. *)
(* Modified by Theorem Labs, 2026-10: the walk of ctrl_lay_block on image B (fuzz_grant.asan-ubsan), ported from
   image A's closed walk lib/A/Prog/CtrlLayBlock.v (a working branch 5aae1e8a0ce), itself written with proof steps adapted
   from proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v, AC8k.v, AChz.v, ACa2.v and ACb8.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/CtrlLayBlock.v, with its module paths, module names and numbers changed; 805 of its 880 lines of code are new or changed and 987 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/ReacHuntObserveSeg_A.v, with its numbers changed; 494 of its 593 lines of code are new or changed and 781 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YA0o YA0q YCbm YK06 YI0m YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC44 YC8g YC8i YXcalls YCbj.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1g YC1h YC1i YC45 YC4b YC7k YC81 YC85 YC88 YCbw YCkd YCbf YCj1 YCja YCjr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ClassifyCore ReacDiscoClassifyOnSegment ReacDiscoTableObserve.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require ReacFrameCleanLen.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_classify_c disco_table_c hunt_c reac_disco_table_observe_c reac_frame_clean_len_c reac_hunt_observe_c
HuntObsFacts HuntObsLib.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacHuntObserveCore.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
Context {PO : PAObjImg lib_both3_0_listing}.
Context {PW : PAWinImg lib_both3_0_listing}.
Context {PV : PAObjVal lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA AS___asan_memcpy).
Hypothesis ABCMP : forall fq : YK11.FPState,
  abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).
Hypothesis ASM1 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TCOS : treac_disco_classify_on_segment_spec B.
Hypothesis TOBS : treac_disco_table_observe_spec B.
Hypothesis HRO : YRo.tfib_ro_unowned B.
#[local] Notation treac_hunt_observe_post := (@ReacHuntObserveCore.treac_hunt_observe_post rc SK PI B).
#[local] Notation EHO := (@ReacHuntObserveCore.EHO rc PI).
#[local] Notation hoC := (@ReacHuntObserveCore.hoC rc PI).
#[local] Notation ho_post := (@ReacHuntObserveCore.ho_post rc SK PI B).
#[local] Notation ho_fsh := (@ReacHuntObserveCore.ho_fsh rc PI).
#[local] Notation ho_cfg := (@ReacHuntObserveCore.ho_cfg rc PI).
#[local] Notation ho_base := (@ReacHuntObserveCore.ho_base rc SK PI B).
#[local] Notation ho_svals := (@ReacHuntObserveCore.ho_svals rc PI).
#[local] Notation ho_extraM := (@ReacHuntObserveCore.ho_extraM rc PI B).
#[local] Notation EHOm := (@ReacHuntObserveCore.EHOm rc PI B).
#[local] Notation ho_seg_T_stmt := (@ReacHuntObserveCore.ho_seg_T_stmt rc SK PI B).
#[local] Notation hoT_aview_frame := (@ReacHuntObserveCore.hoT_aview_frame rc PI).
#[local] Notation hoT_garr_kept := (@ReacHuntObserveCore.hoT_garr_kept rc PI).
Hypothesis ho_entry : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
    (regs : bvmap 5 word) (h n hb hn : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 10 = w64 h ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_HUNT_OBSERVE_STK -> spZ regs <= sp0 ->
  In (hb, hn) (ablocks B lyc Sc) -> hb <= h -> h + 480 <= hb + req_size hn ->
  0 < h -> h mod 8 = 0 -> 0 <= n <= 8 ->
  val_mem SEGS (mrestrict (w_H W) memc) (h + 384) 4 n ->
  st_ok_pi SEGS VAL (EHO regs n (as_uar_cell B)) ss_ho
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + AF_both3_reac_hunt_observe)) memc (seg_rom SEGS))) /\
  sh_ok SEGS HOBx ho_SH (EHO regs n (as_uar_cell B)) (mrestrict (w_H W) memc).
Hypothesis ho_mid_entry : forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F SH (wo : bool) af,
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F ->
  ho_fsh W2 mem2 F SH -> length SH = 16%nat -> Forall (fun z : Z => 0 <= z < 256) SH ->
  (wo = true -> c_out c <> 0 /\ getr regs2 19 = w64 (c_out c)) ->
  st_ok_pi (fx := c_fq c) SEGS VAL (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) (ss_hoM SH wo af)
    (restrict (w_H W2) (mkst (fx := c_fq c) regs2 (Z_to_bv 64 (BASE + af)) mem2 (seg_rom SEGS)))
  /\ img_env VAL A_LIM (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)).

Ltac hoT_ro HS i :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let r := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS
  ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ Ex _ r 0 0
     (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
     ltac:(let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; exfalso; clear - Ho; lia)))
  as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.

Ltac hoT_rr HS rr Hr :=
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict ?Hv ?msx) =>
pose proof (st_ok_pi_restrict_reg Hv Ev ssx msx rr HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ssx) rr) in
change (sr_get (ss_regs ssx) rr) with e in Hr;
cbn [ms_regs restrict mkst sv_denot] in Hr end.

Lemma hoT_ereg : forall (c : hoC) (regs2 : bvmap 5 word) (FL : Z) (n : nat) (rr : bv 5),
  (n <? 32)%nat = true -> Z.of_nat n = bv_unsigned rr -> ew (EHOm c regs2 FL) n = getr regs2 rr.
Proof.
intros c regs2 FL n rr Hn Hr. apply Nat.ltb_lt in Hn. unfold EHOm.
rewrite Eimg_low by (unfold A_TEXT; lia).
exact (ew_Ereg_nat regs2 _ n rr Hr).
Qed.

Lemma hoT_eFL : forall (c : hoC) (regs2 : bvmap 5 word) (FL : Z),
  ew (EHOm c regs2 FL) 33 = Z_to_bv 64 FL.
Proof.
intros c regs2 FL. unfold EHOm. rewrite Eimg_low by (unfold A_TEXT; lia).
exact (ew_Ereg_extra regs2 _ 1).
Qed.

Lemma hoT_euar : forall (c : hoC) (regs2 : bvmap 5 word) (FL : Z),
  ew (EHOm c regs2 FL) 59 = Z_to_bv 64 (as_uar_cell B).
Proof.
intros c regs2 FL. unfold EHOm. rewrite Eimg_low by (unfold A_TEXT; lia).
change 59%nat with (32 + 27)%nat. rewrite ew_Ereg_extra. unfold ho_extraM.
rewrite (map_nth (Z_to_bv 64) ([SB; FL] ++ ho_svals c ++ repeat 0 12 ++ [as_uar_cell B]) 0 27).
unfold ho_svals. cbn [List.seq map nth app repeat]. reflexivity.
Qed.

Lemma hoT_esav : forall (c : hoC) (regs2 : bvmap 5 word) (FL : Z) (j n : nat),
  (j <? 13)%nat = true -> n = (34 + j)%nat -> ew (EHOm c regs2 FL) n = getr (c_regs c) (ho_sreg j).
Proof.
intros c regs2 FL j n Hj ->. apply Nat.ltb_lt in Hj. unfold EHOm.
rewrite Eimg_low by (unfold A_TEXT; lia).
replace (34 + j)%nat with (32 + (2 + j))%nat by lia. rewrite ew_Ereg_extra.
unfold ho_extraM.
rewrite (map_nth (Z_to_bv 64) ([SB; FL] ++ ho_svals c ++ repeat 0 12 ++ [as_uar_cell B]) 0 (2 + j)).
cbn [app nth Nat.add].
do 13 (destruct j as [|j];
  [unfold ho_svals, ho_sreg; cbn [List.seq map nth app]; apply Z_to_bv_bv_unsigned|]).
exfalso. lia.
Qed.

Lemma hoT_div_rng : forall fa n, 4096 <= fa -> 0 <= n -> fa + n <= 140737479966720 ->
  512 <= fa / 8 /\ fa / 8 + n / 8 <= 17592184995840.
Proof. intros fa n H1 H2 H3. split; Z.div_mod_to_equations; lia. Qed.

Lemma hoT_shsep : forall F fa n x, 0 <= F -> 0 <= fa -> 0 <= n ->
  (F + 128 <= fa \/ fa + n <= F) -> fa / 8 <= x < fa / 8 + n / 8 -> ~ (F / 8 <= x < F / 8 + 16).
Proof. intros F fa n x H1 H2 H3 H4 H5. Z.div_mod_to_equations. lia. Qed.

Lemma hoT_obs_len : forall (T G T' : list byte) (ow now ret : Z),
  length T = 400%nat -> length G = 24%nat -> disco_table_c.tbl_T1 T ->
  reac_disco_table_observe_c.observe_model T G ow now T' ret -> length T' = 400%nat.
Proof.
intros T G T' ow now ret LT LG T1 (q & FR & HD). unfold disco_table_c.tbl_T1 in T1.
destruct HD as [(Hq & E) | [(Hq & HN & E) | (Hq & HN & E)]].
- destruct FR as [(X1 & _) | (X1 & _)]; [exfalso; lia|].
  exact (proj1 (reac_disco_table_observe.mf_known T G ow now q T' ret LT LG ltac:(lia) E)).
- exact (proj1 (reac_disco_table_observe.mf_full T T' ret LT E)).
- exact (proj1 (reac_disco_table_observe.mf_new T G ow now T' ret LT LG ltac:(lia) E)).
Qed.

Lemma hoT_ans_len : forall (T G A : list byte),
  length T = 400%nat -> length G = 24%nat -> disco_table_c.tbl_T1 T ->
  reac_hunt_observe_c.ho_answer T G A -> length A = 24%nat.
Proof.
intros T G A LT LG T1 (q & FR & EA). subst A. unfold disco_table_c.tbl_T1 in T1.
destruct (Z.ltb_spec q 0) as [Hq|Hq]; [exact LG|].
assert (Hqn : 0 <= q < 8) by (destruct FR as [(E1 & _) | (R1 & _)]; lia).
unfold reac_hunt_observe_c.ho_entry. rewrite !length_app.
rewrite (HuntObsLib.len_sub G 0 8 ltac:(lia) ltac:(rewrite LG; cbn; lia)).
rewrite (HuntObsLib.len_sub T (48 * q + 8) 9 ltac:(lia) ltac:(rewrite LT; cbn; lia)).
rewrite (HuntObsLib.len_sub G 17 3 ltac:(lia) ltac:(rewrite LG; cbn; lia)).
rewrite (HuntObsLib.len_sub T (48 * q + 20) 4 ltac:(lia) ltac:(rewrite LT; cbn; lia)).
reflexivity.
Qed.

Lemma ho_segT : ho_seg_T_stmt.
Proof.
unfold ho_seg_T_stmt.
intros c fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F H2 r HB R20 Hr HFSH HOK HM.
assert (HrB : In r [-1; 0; 1])
  by (cbn [In]; destruct Hr as [ -> | [ -> | -> ] ]; [left | right; left | right; right; left]; reflexivity).
clear Hr.
pose proof HB as (HPRE & HMID & HSP1 & HFe & HREGS & HSAVED).
pose proof HMID as (HJ & HFRS & HFA & HPERM & HKEPT & HROD & HGH & HLH & HFLw & HKLE).
pose proof HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R21 & R24 & R25).
pose proof HPRE as (PJ & PRO & PRA & PRA4 & PGP & PTP & PAL & PWIN & PSP & PDEP & PLEN & PNOW &
  POUT & PH0 & PH8 & PIN & PHB & PHE & PHW & PHOK & PFBL & PHG & PF50 & POUTF & PKM & PKT).
pose proof HKEPT as (KP1 & KP2 & KP3 & KP4 & KP5 & KP6).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 &
  (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
destruct PJ as (mdc & PJ0).
pose proof PJ0 as (HARc & _ & _ & _ & _ & HFRSc & _).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
pose proof HSP1 as (HSP1a & HSP1b & HSP1c).
clear HSP1a HSP1c PAL Hsp0al PH8 Hbot Htop2 Htop PDEP.
assert (HSTK : REAC_HUNT_OBSERVE_STK = 8688) by reflexivity.
assert (HSB : SB = 2147450880) by reflexivity.
assert (HspB : YM05.alloc_ceiling + 8688 <= spZ (c_regs c) <= 2 ^ 47)
  by (clear - PWIN PSP HSTK Hceil Hslo Hshi H47; rewrite HSTK in PWIN; lia).
assert (HinF : In (1, fpos) (frames S2)) by (rewrite HFRS; left; reflexivity).
assert (HFA1 : frame_addr ly2 1 fpos = F) by (rewrite HFA; symmetry; exact HFe).
assert (HFLeq : flag_addr ly2 1 fpos = flag_addr (c_lyc c) 1 fpos).
{ pose proof (HFA 1 fpos) as HX. unfold frame_addr in HX. unfold flag_addr. clear - HX. lia. }
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 1 fpos HAR HinF) as (_ & HFapp & _ & _).
rewrite HFA1 in HFapp. change (fs_frame_bytes 1) with 128 in HFapp.
pose proof (frm_off_imgP B ly2 S2 W2 mem2 md2 1 fpos HAR HinF) as HFimg.
rewrite HFA1 in HFimg. change (fs_frame_bytes 1) with 128 in HFimg.
assert (HFb : 4096 <= F /\ F + 128 <= YM05.alloc_ceiling).
{ clear - HFapp CC1. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. lia. }
assert (HF8r : 512 <= F / 8 /\ F / 8 + 16 <= 17592184995840).
{ pose proof (hoT_div_rng F 128 ltac:(clear - HFb; lia) ltac:(lia) ltac:(clear - HFb CC1; lia)) as HX.
  change (128 / 8) with 16 in HX. exact HX. }
assert (HinH : In (c_hb c, c_hn c) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym HPERM)); exact PIN).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 (c_hb c) (c_hn c) HAR HinH)
  as (_ & Hb4096 & Hbceil & _ & _ & _ & _).
assert (Hhb : 4096 <= c_h c /\ c_h c + 480 <= YM05.alloc_ceiling)
  by (clear - Hb4096 Hbceil PHB PHE; lia).
clear Hb4096 Hbceil.
destruct (FFL ly2 S2 W2 mem2 md2 1 fpos HAR HinF)
  as (_ & HFLown & (_ & HFLnimg) & (HFL4096 & HFLz2 & HFLceil)).
rewrite HFLeq in HFLown, HFLnimg, HFL4096, HFLz2, HFLceil.
assert (HOUTF2 : c_out c <> 0 ->
  (forall a, c_out c <= a < c_out c + 24 ->
     awr_byte (c_STK c) (c_sp0 c) (c_FP c) (ablocks B (c_ly c) (c_S c))
       (ablocks B (c_lyc c) (c_Sc c)) (c_lyc c) (c_own c) a) /\ length (c_O c) = 24%nat).
{ intros Hout. destruct (POUTF Hout) as (HTO & _ & _).
  destruct HTO as (_ & _ & _ & _ & _ & _ & _ & Hwr & HLO & _ & _).
  split; [intros a Ha; exact (proj1 (Hwr a Ha)) | exact HLO]. }
assert (HSAFEB : forall b m a, In (b, m) (ablocks B (c_lyc c) (c_Sc c)) -> b <= a < b + req_size m ->
  ~ (F <= a < F + 128) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 16)
  /\ a <> flag_addr (c_lyc c) 1 fpos /\ 0 <= a < 2 ^ 64).
{ intros b m a Hin Ha.
  assert (Hin2 : In (b, m) (ablocks B ly2 S2))
    by (apply (Permutation_in _ (Permutation_sym HPERM)); exact Hin).
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 b m HAR Hin2)
    as (_ & Hb1 & Hbc & Hba & Hbp & _ & _).
  pose proof (sep_block_frame _ _ LAWS ly2 S2 W2 mem2 md2 b m 1 fpos HAR Hin2 HinF) as Hdj.
  rewrite HFA1 in Hdj. change (fs_frame_bytes 1) with 128 in Hdj.
  unfold zdisjoint in Hdj. cbn [fst snd] in Hdj.
  split; [clear - Hdj Ha; lia|].
  split; [clear - Hba Ha HF8r HSB; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hba; lia|].
  split; [|clear - Hb1 Hbc Ha CC1; lia].
  intros Heq. rewrite <- Heq in HFLown. exact (proj2 (Hbp _ Ha) HFLown). }
assert (HSAFEF : forall cid pos a, In (cid, pos) (frames (c_Sc c)) ->
  (in_zr a (frame_rng (c_lyc c) (cid, pos))
   \/ in_zr a (shadow_addr (frame_addr (c_lyc c) cid pos), fs_frame_bytes cid / 8)) ->
  ~ (F <= a < F + 128) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 16)
  /\ a <> flag_addr (c_lyc c) 1 fpos /\ 0 <= a < 2 ^ 64).
{ intros cid pos a Hin Hz.
  assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite HFRS; right; exact Hin).
  destruct (in_split _ _ Hin) as (l2 & l3 & Esp).
  pose proof (sep_frames_pos _ _ LAWS ly2 S2 W2 mem2 md2 (1, fpos) (cid, pos) [] l2 l3 HAR
    ltac:(rewrite HFRS, Esp; reflexivity)) as Hdj.
  clear Esp.
  unfold zdisjoint, frame_rng in Hdj. cbn [fst snd] in Hdj.
  rewrite HFA1 in Hdj. change (fs_frame_bytes 1) with 128 in Hdj.
  destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 cid pos HAR Hin2)
    as (_ & Hgapp & Hgpres & Hgspres).
  pose proof (frames_bounds _ _ LAWS ly2 S2 W2 mem2 md2 cid pos HAR Hin2) as (Hg1 & Hg2 & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hgn.
  set (fa := frame_addr ly2 cid pos) in *. set (n := fs_frame_bytes cid) in *.
  pose proof Hz as Hz2.
  unfold in_zr, frame_rng, shadow_addr in Hz2. cbn [fst snd] in Hz2.
  rewrite <- (HFA cid pos) in Hz2. rewrite <- SB_SHADOW_OFF in Hz2. fold fa n in Hz2.
  destruct Hz2 as [Hz2 | Hz2].
  - split; [clear - Hdj Hz2; lia|].
    split; [clear - Hgapp Hz2 HF8r HSB;
            unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hgapp; lia|].
    split; [|clear - Hg1 Hg2 Hz2 CC1; lia].
    intros Heq. rewrite <- Heq in HFLown. exact (proj2 (Hgpres _ Hz2) HFLown).
  - pose proof (hoT_div_rng fa n Hg1 Hgn ltac:(clear - Hg2 CC1; lia)) as Hfa8r.
    pose proof (hoT_shsep F fa n (a - SB) ltac:(clear - HFb; lia) ltac:(clear - Hg1; lia) Hgn Hdj
      ltac:(clear - Hz2; lia)) as Hss.
    split; [clear - HFapp Hz2 Hfa8r HSB;
            unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp; lia|].
    split; [clear - Hss; lia|].
    split; [|clear - Hz2 Hfa8r HSB; lia].
    intros Heq. rewrite <- Heq in HFLown.
    destruct (Hgspres (a - (SB + fa / 8)) ltac:(clear - Hz2; lia)) as (_ & Hno).
    apply Hno. unfold shadow_addr. rewrite <- SB_SHADOW_OFF. fold fa.
    replace (SB + fa / 8 + (a - (SB + fa / 8))) with a by (clear; lia).
    exact HFLown. }
assert (HSAFE : forall a,
  awr_byte (c_STK c) (c_sp0 c) (c_FP c) (ablocks B (c_ly c) (c_S c))
    (ablocks B (c_lyc c) (c_Sc c)) (c_lyc c) (c_own c) a ->
  ~ (F <= a < F + 128) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 16)
  /\ a <> flag_addr (c_lyc c) 1 fpos /\ 0 <= a < 2 ^ 64).
{ intros a [Hx | [[_ (b & n & Hin & Hrr)] | [(b & n & Hin & _ & Hrr) | (cid & pos & Hin & Hz)]]].
  - split; [clear - Hx HFb Hceil Hslo; lia|].
    split; [clear - Hx HF8r HSB Hceil Hslo CC1; lia|].
    split; [clear - Hx HFLceil Hceil Hslo; lia|].
    clear - Hx Hslo Hshi H47 Hceil CC1; lia.
  - exact (HSAFEB b n a Hin Hrr).
  - exact (HSAFEB b n a Hin Hrr).
  - apply (HSAFEF cid pos a); [|exact Hz].
    rewrite HFRSc. apply in_or_app. left. exact Hin. }
destruct (ho_mid_entry c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F ho_shC false 0x7344 HB HFSH
  eq_refl ltac:(unfold ho_shC; repeat (apply Forall_cons; [clear; lia|]); apply Forall_nil)
  ltac:(discriminate)) as [HS HEI].
assert (U2 : bv_unsigned (ew (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) 2) = sp1)
  by (rewrite (hoT_ereg c regs2 _ 2 2%bv eq_refl eq_refl), R2;
      apply unsigned_lit_small; clear - HSP1b HspB CC1; lia).
assert (U8 : bv_unsigned (ew (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) 8) = spZ (c_regs c))
  by (rewrite (hoT_ereg c regs2 _ 8 8%bv eq_refl eq_refl), R8;
      apply unsigned_lit_small; clear - HspB CC1; lia).
assert (U18 : bv_unsigned (ew (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) 18) = F)
  by (rewrite (hoT_ereg c regs2 _ 18 18%bv eq_refl eq_refl), R18;
      apply unsigned_lit_small; clear - HFb CC1; lia).
assert (U21 : bv_unsigned (ew (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) 21) = c_h c)
  by (rewrite (hoT_ereg c regs2 _ 21 21%bv eq_refl eq_refl), R21;
      apply unsigned_lit_small; clear - Hhb CC1; lia).
assert (U24 : bv_unsigned (ew (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) 24) = SB + F / 8)
  by (rewrite (hoT_ereg c regs2 _ 24 24%bv eq_refl eq_refl), R24;
      apply unsigned_lit_small; clear - HF8r HSB; lia).
assert (E33 : ew (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) 33
              = Z_to_bv 64 (flag_addr (c_lyc c) 1 fpos)) by apply hoT_eFL.
assert (U33 : bv_unsigned (ew (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) 33)
              = flag_addr (c_lyc c) 1 fpos)
  by (rewrite E33; apply unsigned_lit_small; clear - HFL4096 HFLceil CC1; lia).
assert (E18 : ew (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) 18 = getr regs2 18)
  by (apply hoT_ereg; reflexivity).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (25%bv : bv 5) (SOff 18 0) HS
  ltac:(vm_compute; reflexivity)
  ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E18, Z.add_0_r, Z_to_bv_bv_unsigned;
        rewrite R18, R25; reflexivity)) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.
hoT_ro HS 0%nat. hoT_ro HS 1%nat. hoT_ro HS 8%nat.
pose (RUNP := SRr_run_pi_AJ (fx := c_fq c) B LAWS).
unfold ho_cfg.
paj_run_sh RUNP HS HJ.
{ intros a (rg & Hrg & Hrng). cbn [ss_mem In] in Hrg.
  destruct Hrg as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrng;
  rewrite ?U2, ?U8, ?U18, ?U24, ?U21 in Hrng;
  try (exfalso; clear - Hrng; lia).
  - right; right; right. exists 1, fpos. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite HFA1. change (fs_frame_bytes 1) with 128.
    clear - Hrng; lia.
  - right; right; right. exists 1, fpos. split; [left; reflexivity|]. right.
    unfold in_zr, shadow_addr. cbn [fst snd]. rewrite HFA1, <- SB_SHADOW_OFF.
    change (fs_frame_bytes 1 / 8) with 16. clear - Hrng; lia. }
rename ms into msA. rename mat into matA. rename HFr into HFrA. rename HG into HGA. clear HF.
assert (HUPA : forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 128) ->
  ~ (SB + F / 8 <= a < SB + F / 8 + 16) ->
  aview SEGS (w_H W2) (ms_mem msA) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hn1 Hn2. apply (hoT_aview_frame _ _ W2 mem2 (ms_mem msA) a HFrA Ha).
  intros (rg & Hrg & Hrng). cbn [ss_mem In] in Hrg.
  destruct Hrg as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrng;
  rewrite ?U2, ?U8, ?U18, ?U24, ?U21 in Hrng; clear - Hrng Hn1 Hn2; lia. }
pose proof HJ as (HAR2 & _).
destruct (FFL ly2 S2 W2 (ms_mem msA) _ 1 fpos HAR2 HinF) as (HFLpres & _ & _ & _).
rewrite HFLeq in HFLpres.
destruct (al_frames _ _ LAWS ly2 S2 W2 (ms_mem msA) _ 1 fpos HAR2 HinF)
  as (_ & _ & HFpres & HFSpres).
rewrite HFA1 in HFpres, HFSpres.
change (fs_frame_bytes 1) with 128 in HFpres, HFSpres.
assert (HnoF : forall a, F <= a < F + 128 -> ~ aowned B ly2 S2 a)
  by (intros a Ha; exact (proj2 (HFpres a Ha))).
assert (HnoFS : forall a, SB + F / 8 <= a < SB + F / 8 + 16 -> ~ aowned B ly2 S2 a).
{ intros a Ha Hown.
  destruct (HFSpres (a - (SB + F / 8)) ltac:(change (128 / 8) with 16; clear - Ha; lia)) as (_ & Hno).
  apply Hno. unfold shadow_addr. rewrite <- SB_SHADOW_OFF.
  replace (SB + F / 8 + (a - (SB + F / 8))) with a by (clear; lia). exact Hown. }
destruct (al_blocks _ _ LAWS ly2 S2 W2 (ms_mem msA) _ (c_hb c) (c_hn c) HAR2 HinH)
  as (_ & _ & _ & _ & Hbpres & _ & _).
assert (HnoH : forall a, c_h c <= a < c_h c + 480 -> ~ aowned B ly2 S2 a)
  by (intros a Ha; exact (proj2 (Hbpres a ltac:(clear - Ha PHB PHE; lia)))).
clear HFpres HFSpres Hbpres.
pose proof (@pa_obj_img _ lib_both3_0_listing PI 0 ltac:(apply Nat.ltb_lt; reflexivity)) as Hob241.
pose proof (@pa_obj_img _ lib_both3_0_listing PI 1 ltac:(apply Nat.ltb_lt; reflexivity)) as Hob242.
pose proof (@pa_obj_img _ lib_both3_0_listing PI 12 ltac:(apply Nat.ltb_lt; reflexivity)) as Hob253.
cbv [A_OBJ Nat.add] in Hob241, Hob242, Hob253.
pose proof (palf_uar_img B TLF) as Huar.
assert (U241 : bv_unsigned (ew (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) 241) = VAL 241%nat)
  by (rewrite (img_env_atomP _ 241%nat HEI ltac:(clear - HEI; unfold A_TEXT, A_LIM; lia));
      apply unsigned_lit_small; pose proof (pa_val_range 241%nat) as VR; clear - VR; lia).
assert (U242 : bv_unsigned (ew (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) 242) = VAL 242%nat)
  by (rewrite (img_env_atomP _ 242%nat HEI ltac:(clear - HEI; unfold A_TEXT, A_LIM; lia));
      apply unsigned_lit_small; pose proof (pa_val_range 242%nat) as VR; clear - VR; lia).
assert (U253 : bv_unsigned (ew (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) 253) = VAL 253%nat)
  by (rewrite (img_env_atomP _ 253%nat HEI ltac:(clear - HEI; unfold A_TEXT, A_LIM; lia));
      apply unsigned_lit_small; pose proof (pa_val_range 253%nat) as VR; clear - VR; lia).
assert (U59 : bv_unsigned (ew (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) 59) = as_uar_cell B)
  by (rewrite hoT_euar; apply unsigned_lit_small;
      clear - Huar; unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Huar; lia).
assert (HFLoff : flag_addr (c_lyc c) 1 fpos + 1 <= YImgTop.IMG_LO
                 \/ YImgTop.IMG_TOP <= flag_addr (c_lyc c) 1 fpos)
  by exact (zone2_img _ _ HFLz2).
hoT_ro HS 6%nat. hoT_ro HS 7%nat.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 33%nat) 0 1 0 1 []) HS eq_refl
  ltac:(unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem
             restrict mkst];
        rewrite U33; split; [clear - HFL4096 HFLceil CC1; lia|];
        split; [clear - HFL4096 HFLceil CC1; lia|]; split; [|apply Forall_nil];
        let o := fresh "o" in let Ho := fresh "Ho" in
        intros o Ho; apply (apresent_writable SEGS);
        replace (flag_addr (c_lyc c) 1 fpos + o) with (flag_addr (c_lyc c) 1 fpos)
          by (clear - Ho; lia);
        exact HFLpres)
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
          let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
        rewrite ?U2, ?U8, ?U18, ?U21, ?U24, ?U33, ?U241, ?U242, ?U253, ?U59;
        repeat split;
        first [ clear - HSP1b HspB HFLceil; lia
              | clear - HFLoff Hob241 Hob242 Hob253 Huar;
                unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia
              | lazymatch goal with |- ?fl + 1 <= ?x + ?l \/ ?x + ?h <= ?fl + 0 =>
                  let Hlt1 := fresh "Hlt1" in let Hge1 := fresh "Hge1" in
                  let Hlt2 := fresh "Hlt2" in let Hge2 := fresh "Hge2" in
                  destruct (Z_lt_ge_dec fl (x + l)) as [Hlt1|Hge1]; [left; clear - Hlt1; lia|];
                  destruct (Z_lt_ge_dec fl (x + h)) as [Hlt2|Hge2]; [exfalso | right; clear - Hge2; lia];
                  first [ apply (HnoF fl); [clear - Hge1 Hlt2; lia | exact HFLown]
                        | apply (HnoFS fl); [clear - Hge1 Hlt2; lia | exact HFLown]
                        | apply (HnoH fl); [clear - Hge1 Hlt2; lia | exact HFLown] ] end ])) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.
pose (RUNF := aj_flag_store_pi (fx := c_fq c) B LAWS ML ASF FFL).
paj_run_flag_sh RUNF HS HJ.
{ clear; lia. }
{ intros a (rg & Hrg & Hrng). cbn [ss_mem In] in Hrg.
  destruct Hrg as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrng;
  rewrite ?U2, ?U8, ?U18, ?U24, ?U21, ?U33 in Hrng;
  try (exfalso; clear - Hrng; lia).
  right. rewrite HFLeq. clear - Hrng. lia. }
{ flag0 E33 HFLeq. }
rename ms into msB. rename mat into matB. rename HFr into HFrB. rename HG into HGB. clear HF.
assert (HUPB : forall a, 0 <= a < 2 ^ 64 -> a <> flag_addr (c_lyc c) 1 fpos ->
  aview SEGS (w_H W2) (ms_mem msB) a = aview SEGS (w_H W2) (ms_mem msA) a).
{ intros a Ha Hn. apply (hoT_aview_frame _ _ W2 (ms_mem msA) (ms_mem msB) a HFrB Ha).
  intros (rg & Hrg & Hrng). cbn [ss_mem In] in Hrg.
  destruct Hrg as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrng;
  rewrite ?U2, ?U8, ?U18, ?U24, ?U21, ?U33 in Hrng; clear - Hrng Hn; lia. }
assert (HUP : forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 128) ->
  ~ (SB + F / 8 <= a < SB + F / 8 + 16) -> a <> flag_addr (c_lyc c) 1 fpos ->
  aview SEGS (w_H W2) (ms_mem msB) a = aview SEGS (w_H W2) mem2 a)
  by (intros a Ha Hx1 Hx2 Hx3; rewrite (HUPB a Ha Hx3); exact (HUPA a Ha Hx1 Hx2)).
assert (HPRES : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msB) a)
  by (intros a Ha; eapply apresent_grows; [exact HGB|];
      eapply apresent_grows; [exact HGA | exact Ha]).
assert (HGOUT : forall (A : list byte), length A = 24%nat -> c_out c <> 0 ->
  garr8 SEGS (mrestrict (w_H W2) mem2) (c_out c) (map (fun b : byte => bv_unsigned b) A) ->
  garr8 SEGS (mrestrict (w_H W2) (ms_mem msB)) (c_out c)
    (map (fun b : byte => bv_unsigned b) A)).
{ intros A LA Hout HGa. apply (hoT_garr_kept W2 mem2 (ms_mem msB)); [|exact HGa].
  intros i Hi. rewrite length_map, LA in Hi.
  destruct (HSAFE i (proj1 (HOUTF2 Hout) i ltac:(clear - Hi; cbn in Hi; lia))) as (N1 & N2 & N3 & N4).
  exact (HUP i N4 N1 N2 N3). }
assert (HGHUNT : garr8 SEGS (mrestrict (w_H W2) (ms_mem msB)) (c_h c)
  (map (fun b : byte => bv_unsigned b) H2)).
{ apply (hoT_garr_kept W2 mem2 (ms_mem msB)); [|exact HGH].
  intros i Hi. rewrite length_map, HLH in Hi.
  destruct (HSAFE i (PHW i ltac:(clear - Hi; cbn in Hi; lia))) as (N1 & N2 & N3 & N4).
  exact (HUP i N4 N1 N2 N3). }
assert (HFRS2 : frames (stack_free_state 1 fpos S2) = frames (c_Sc c)).
{ replace (frames (stack_free_state 1 fpos S2)) with (del_pos (frames S2) 1 fpos) by reflexivity.
  rewrite HFRS. cbn [del_pos]. rewrite !Z.eqb_refl. reflexivity. }
assert (HAB : ablocks B ly2 (stack_free_state 1 fpos S2) = ablocks B ly2 S2)
  by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
hoT_rr HS (1%bv : bv 5) Q1.
rewrite (hoT_esav c regs2 (flag_addr (c_lyc c) 1 fpos) 0%nat 34%nat eq_refl eq_refl),
  Z.add_0_r, Z_to_bv_bv_unsigned in Q1.
cbn [ho_sreg nth] in Q1.
eapply (paj_ret_at (fx := c_fq c) (PL := PL_both3_0) (PI := PI) W2 _ _ _ _ _ HS eq_refl
  ltac:(vm_compute; reflexivity)).
intros mat9.
unfold ho_post, treac_hunt_observe_post. cbv beta.
lazymatch goal with |- exists _ _ _ _ _ _ _ _, mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ =>
  exists (c_fq c), ly2, (stack_free_state 1 fpos S2), rg, mm, mdx, r, H2 end.
split; [rewrite Q1, PRA; reflexivity|].
split; [intros kq _; reflexivity|].
split; [left; reflexivity|].
split; [eapply ajournal_mono_k;
        [eapply ajournal_materialize; first [exact LAWS | exact (@pa_segs_low _ _ PI) | exact HJ]
        | clear - HKLE; lia]|].
split.
{ apply aregs_preserved_eqs.
  - hoT_rr HS (2%bv : bv 5) Q2.
    rewrite (hoT_ereg c regs2 _ 8 8%bv eq_refl eq_refl), R8,
      Z.add_0_r, Z_to_bv_bv_unsigned in Q2.
    unfold w64, spZ in Q2. rewrite Z_to_bv_bv_unsigned in Q2. exact Q2.
  - hoT_rr HS (3%bv : bv 5) Q3.
    rewrite (hoT_ereg c regs2 _ 3 3%bv eq_refl eq_refl), R3,
      Z.add_0_r, Z_to_bv_bv_unsigned in Q3. rewrite Q3, PGP. reflexivity.
  - hoT_rr HS (4%bv : bv 5) Q4.
    rewrite (hoT_ereg c regs2 _ 4 4%bv eq_refl eq_refl), R4,
      Z.add_0_r, Z_to_bv_bv_unsigned in Q4. rewrite Q4, PTP. reflexivity.
  - hoT_rr HS (8%bv : bv 5) Q8.
    rewrite (hoT_esav c regs2 _ 1%nat 35%nat eq_refl eq_refl),
      Z.add_0_r, Z_to_bv_bv_unsigned in Q8. cbn [ho_sreg nth] in Q8. exact Q8.
  - hoT_rr HS (9%bv : bv 5) Q9.
    rewrite (hoT_esav c regs2 _ 2%nat 36%nat eq_refl eq_refl),
      Z.add_0_r, Z_to_bv_bv_unsigned in Q9. cbn [ho_sreg nth] in Q9. exact Q9.
  - hoT_rr HS (18%bv : bv 5) QA.
    rewrite (hoT_esav c regs2 _ 3%nat 37%nat eq_refl eq_refl),
      Z.add_0_r, Z_to_bv_bv_unsigned in QA. cbn [ho_sreg nth] in QA. exact QA.
  - hoT_rr HS (19%bv : bv 5) QB.
    rewrite (hoT_esav c regs2 _ 4%nat 38%nat eq_refl eq_refl),
      Z.add_0_r, Z_to_bv_bv_unsigned in QB. cbn [ho_sreg nth] in QB. exact QB.
  - hoT_rr HS (20%bv : bv 5) QC.
    rewrite (hoT_esav c regs2 _ 5%nat 39%nat eq_refl eq_refl),
      Z.add_0_r, Z_to_bv_bv_unsigned in QC. cbn [ho_sreg nth] in QC. exact QC.
  - hoT_rr HS (21%bv : bv 5) QD.
    rewrite (hoT_esav c regs2 _ 6%nat 40%nat eq_refl eq_refl),
      Z.add_0_r, Z_to_bv_bv_unsigned in QD. cbn [ho_sreg nth] in QD. exact QD.
  - hoT_rr HS (22%bv : bv 5) QE.
    rewrite (hoT_esav c regs2 _ 7%nat 41%nat eq_refl eq_refl),
      Z.add_0_r, Z_to_bv_bv_unsigned in QE. cbn [ho_sreg nth] in QE. exact QE.
  - hoT_rr HS (23%bv : bv 5) QF.
    rewrite (hoT_esav c regs2 _ 8%nat 42%nat eq_refl eq_refl),
      Z.add_0_r, Z_to_bv_bv_unsigned in QF. cbn [ho_sreg nth] in QF. exact QF.
  - hoT_rr HS (24%bv : bv 5) QG.
    rewrite (hoT_esav c regs2 _ 9%nat 43%nat eq_refl eq_refl),
      Z.add_0_r, Z_to_bv_bv_unsigned in QG. cbn [ho_sreg nth] in QG. exact QG.
  - hoT_rr HS (25%bv : bv 5) QH.
    rewrite (hoT_esav c regs2 _ 10%nat 44%nat eq_refl eq_refl),
      Z.add_0_r, Z_to_bv_bv_unsigned in QH. cbn [ho_sreg nth] in QH. exact QH.
  - hoT_rr HS (26%bv : bv 5) QI.
    rewrite (hoT_esav c regs2 _ 11%nat 45%nat eq_refl eq_refl),
      Z.add_0_r, Z_to_bv_bv_unsigned in QI. cbn [ho_sreg nth] in QI. exact QI.
  - hoT_rr HS (27%bv : bv 5) QJ.
    rewrite (hoT_esav c regs2 _ 12%nat 46%nat eq_refl eq_refl),
      Z.add_0_r, Z_to_bv_bv_unsigned in QJ. cbn [ho_sreg nth] in QJ. exact QJ. }
split.
{ hoT_rr HS (10%bv : bv 5) QK.
  rewrite (hoT_ereg c regs2 _ 20 20%bv eq_refl eq_refl), R20,
    Z.add_0_r, Z_to_bv_bv_unsigned in QK. exact QK. }
split; [exact HFRS2|].
split; [rewrite HAB; exact HPERM|].
split.
{ split.
  { intros a Ha1 Ha2 Ha3.
    rewrite (HUP a ltac:(clear - Ha1 CC1; lia) ltac:(clear - Ha1 HFb; lia)
      ltac:(clear - Ha1 HF8r HSB CC1; lia) ltac:(clear - Ha1 HFLceil; lia)).
    exact (KP1 a Ha1 Ha2 Ha3). }
  split.
  { intros b m i Hin Hi Hw.
    destruct (HSAFEB b m (b + i) Hin ltac:(clear - Hi; lia)) as (N1 & N2 & N3 & N4).
    rewrite (HUP (b + i) N4 N1 N2 N3). exact (KP2 b m i Hin Hi Hw). }
  split.
  { intros a Hi Ho He.
    pose proof (@pa_segs_low _ _ PI a Hi) as Hlow.
    pose proof (@pa_img_range _ _ PI a Hi) as Hrng.
    rewrite (HUP a ltac:(clear - Hlow; unfold kLowMemEnd in Hlow; lia)
      ltac:(clear - Hrng HFimg; unfold off_img in HFimg; lia)
      ltac:(clear - Hlow HF8r HSB; unfold kLowMemEnd in Hlow; lia)
      ltac:(intros Heq; rewrite Heq in Hi; exact (HFLnimg Hi))).
    exact (KP3 a Hi Ho He). }
  split.
  { intros cid pos a Hin Hz Hw.
    destruct (HSAFEF cid pos a Hin Hz) as (N1 & N2 & N3 & N4).
    rewrite (HUP a N4 N1 N2 N3). exact (KP4 cid pos a Hin Hz Hw). }
  split.
  { intros a Ha1 Ha2 Ha3. apply HPRES. exact (KP5 a Ha1 Ha2 Ha3). }
  { intros a Ha. apply HPRES. exact (KP6 a Ha). } }
split; [exact HGHUNT|].
split; [exact HOK|].
split; [cbn [In] in HrB; destruct HrB as [E|[E|[E|[]]]]; rewrite <- E;
         [left | right; left | right; right]; reflexivity|].
unfold tho_model in HM |- *. cbv zeta in HM |- *.
destruct HM as [HMF HMO]. split.
- intros Hne. destruct (HMF Hne) as (EM1 & EM2 & EM3). split; [exact EM1|].
  split; [exact EM2|]. intros Hout.
  exact (HGOUT (c_O c) (proj2 (HOUTF2 Hout)) Hout (EM3 Hout)).
- intros Hne. destruct (HMO Hne) as (T' & cc & OM & EM1 & EM2 & EM3).
  exists T', cc. split; [exact OM|]. split; [exact EM1|]. split; [exact EM2|].
  intros Hout. destruct (EM3 Hout) as (A & HA & HOA & HFA2). exists A.
  split; [exact HA|]. split; [|exact HFA2].
  destruct PHOK as (LHH & TOKx & _ & _).
  assert (LT : length (disco_table_c.sub (c_H c) 0 400) = 400%nat)
    by (apply HuntObsLib.len_sub; [clear; lia | rewrite LHH; cbn; clear; lia]).
  assert (LG : length (disco_classify_c.sight (c_FB c)
      (reac_frame_clean_len_c.reac_frame_clean_len_model (c_len c))) = 24%nat)
    by (apply HuntObsFacts.sight_len; exact PFBL).
  destruct TOKx as (X1 & X2 & X3 & X4).
  assert (LT' : length T' = 400%nat)
    by (exact (hoT_obs_len _ _ T' 0 (c_now c) cc LT LG X1 OM)).
  assert (TT1' : disco_table_c.tbl_T1 T').
  { destruct (reac_disco_table_observe.observe_model_tbl _ _ 0 (c_now c) T' cc LT LG X1 X2 X3
      (proj1 (HuntObsFacts.sight_ok (c_FB c)
        (reac_frame_clean_len_c.reac_frame_clean_len_model (c_len c)) PFBL))
      (proj2 (HuntObsFacts.sight_ok (c_FB c)
        (reac_frame_clean_len_c.reac_frame_clean_len_model (c_len c)) PFBL)) OM) as (Y1 & _).
    exact Y1. }
  exact (HGOUT A (hoT_ans_len T' _ A LT' LG TT1' HA) Hout HOA).
Qed.

End h.
End f.
End d.
