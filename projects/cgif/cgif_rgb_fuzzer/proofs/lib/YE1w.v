(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0l YK0s YK0o YQ0k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ0a YQ04 YQ05 YQ0e YQ02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10 YP0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o YA0k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE1j YF8v YE1o YE1p YE07 YE09 YE1s YE1r YE06 YF8r YE04 YE0v YE1q.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section g. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma seg_rom_none_band {imgk : img} : forall a, in_band_rw a -> seg_rom tfxsegs (Z_to_bv 64 a) = None.
Proof.
intros a Ha. img_apply YF8r.seg_rom_none_off. unfold YF8r.off_img, YF8r.TFX_IMG_LO, YF8r.TFX_IMG_END.
unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha. img_lia.
Qed.
Definition F_STDOUT {imgk : img} : Z := (0xa6840 + D_10f0).
Definition STDOUT_BUFA {imgk : img} : Z := (0x5fd860 + D_10c0).
Definition STDOUT_BSZ : Z := 1024.
Definition FMT_d {imgk : img} : Z := (0x14861 + D_20).
Definition RA_PAD {imgk : img} : Z := (0x98974 + D_10ec).
Definition OSP_PC : Z := -912.
Definition PAD_OFF : Z := -736.
Definition stdout_fields0 {imgk : img} : list (Z * N * Z) :=
[(0, 4%N, 5); (4, 4%N, 0); (8, 8%N, 0); (16, 8%N, 0); (24, 8%N, (0x96d9c + D_10ec)); (32, 8%N, 0); (40, 8%N, 0); (48, 8%N, 0); (56, 8%N, 0); (64, 8%N, 0);
(72, 8%N, (0x97b8c + D_10ec)); (80, 8%N, (0x96ee0 + D_10ec)); (88, 8%N, STDOUT_BUFA); (96, 8%N, STDOUT_BSZ); (104, 8%N, 0); (112, 8%N, 0); (120, 8%N, 1);
(128, 8%N, 0); (136, 4%N, 0); (140, 4%N, 0xffffffff); (144, 8%N, 10);
(152, 8%N, 0); (160, 8%N, 0); (168, 8%N, 0); (176, 8%N, 0); (184, 8%N, 0); (192, 8%N, 0); (200, 8%N, 0); (208, 8%N, 0);
(216, 8%N, 0); (224, 8%N, 0)].
Definition stdout_fields1 {imgk : img} : list (Z * N * Z) :=
[(0, 4%N, 5); (4, 4%N, 0); (8, 8%N, 0); (16, 8%N, 0); (24, 8%N, (0x96d9c + D_10ec)); (32, 8%N, STDOUT_BUFA + STDOUT_BSZ); (48, 8%N, 0);
(56, 8%N, STDOUT_BUFA); (64, 8%N, 0); (72, 8%N, (0x96ee8 + D_10ec)); (80, 8%N, (0x96ee0 + D_10ec)); (88, 8%N, STDOUT_BUFA); (96, 8%N, STDOUT_BSZ);
(104, 8%N, 0); (112, 8%N, 0); (120, 8%N, 1); (128, 8%N, 0); (136, 4%N, 0xffffffff); (140, 4%N, 0xffffffff); (144, 4%N, 0xffffffff);
(152, 8%N, 0); (160, 8%N, 0); (168, 8%N, 0); (176, 8%N, 0); (184, 8%N, 0); (192, 8%N, 0); (200, 8%N, 0); (208, 8%N, 0);
(216, 8%N, 0); (224, 8%N, 0)].
Definition ofile_is {imgk : img} (flds : list (Z * N * Z)) (m : word -> option byte) : Prop :=
Forall (fun f => match f with (o, n, v) => val_mem tfxsegs m (F_STDOUT + o) (N.to_nat n) v end) flds.
Definition stdout_pristine {imgk : img} : (word -> option byte) -> Prop := ofile_is stdout_fields0.
Definition stdout_mid {imgk : img} (wp : Z) (m : word -> option byte) : Prop :=
ofile_is stdout_fields1 m /\ val_mem tfxsegs m (F_STDOUT + 40) 8 wp.
Definition fo_chunks {imgk : img} (flds : list (Z * N * Z)) : list YQ0b.chunk :=
map (fun f => match f with (o, n, v) => YQ0b.mkChunk (F_STDOUT + o) (CVal n (SLit v)) end) flds.
Definition vo_regions {imgk : img} (fchunks : list YQ0b.chunk) : smem :=
[ YQ0b.mkRegion (Some 2%nat) (- VF_STK) 0 (- VF_STK) 0 [];
YQ0b.mkRegion None F_STDOUT (F_STDOUT + FILE_SZ) F_STDOUT (F_STDOUT + FILE_SZ) fchunks;
YQ0b.mkRegion None A_GOT_canary (A_GOT_canary + 8) 0 0 [YQ0b.mkChunk A_GOT_canary (CVal 8 (SLit A_canary))];
YQ0b.mkRegion None A_canary (A_canary + 8) 0 0 [YQ0b.mkChunk A_canary (CVal 8 (SOff 33 0))];
YQ0b.mkRegion (Some 12%nat) 0 8 0 0 [YQ0b.mkChunk 0 (CVal 8 (SLit 0))];
img_ro_region ].
Definition vo_sr {imgk : img} : list sv := sr_set (sr_set sr_atoms (10%bv : bv 5) (SLit F_STDOUT)) (11%bv : bv 5) (SLit FMT_d).
Definition vo_facts0 : facts := mkFacts [ (2%nat, mkAF (2 ^ 44) (2 ^ 47) 4); (12%nat, mkAF (2 ^ 44) (2 ^ 47) 3) ] [] [].
Definition vo_facts1 {imgk : img} : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 44) (2 ^ 47) 4); (12%nat, mkAF (2 ^ 44) (2 ^ 47) 3); (34%nat, mkAF STDOUT_BUFA (STDOUT_BUFA + STDOUT_BSZ - 2) 0) ] [] [].
Definition ss_vo0 {imgk : img} : sstate := mkSS A_vfprintf vo_sr (vo_regions (fo_chunks stdout_fields0)) None vo_facts0.
Definition ss_vo1 {imgk : img} : sstate :=
mkSS A_vfprintf vo_sr (vo_regions (YQ0b.mkChunk (F_STDOUT + 40) (CVal 8 (SOff 34 0)) :: fo_chunks stdout_fields1)) None vo_facts1.
Definition vo_file {imgk : img} (a : Z) : Prop := F_STDOUT <= a < F_STDOUT + FILE_SZ.
Definition vo_mut {imgk : img} (blo bhi : Z) (a : Z) : Prop := vo_file a \/ blo <= a < bhi.
Lemma stdout_img_bytes_ok {imgk : img} : zallb (img_byte_ok tfxsegs) F_STDOUT (Z.to_nat FILE_SZ) = true.
Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma stdout_buf_img_bytes_ok {imgk : img} : zallb (img_byte_ok tfxsegs) STDOUT_BUFA (Z.to_nat STDOUT_BSZ) = true.
Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma vo_mut_img {imgk : img} : forall blo bhi a, STDOUT_BUFA <= blo -> bhi <= STDOUT_BUFA + STDOUT_BSZ ->
vo_mut blo bhi a -> img_byte_ok tfxsegs a = true.
Proof.
intros blo bhi a Hlo Hhi [Hf|Hb].
- unfold vo_file in Hf. img_exact (zallb_sound _ _ _ a stdout_img_bytes_ok ltac:(img_try (unfold FILE_SZ in *; img_lia))).
- img_exact (zallb_sound _ _ _ a stdout_buf_img_bytes_ok ltac:(img_try (unfold STDOUT_BSZ in *; img_lia))).
Qed.
Lemma vo_mut_dec {imgk : img} : forall blo bhi a, vo_mut blo bhi a \/ ~ vo_mut blo bhi a.
Proof. intros blo bhi a. unfold vo_mut, vo_file. img_lia. Qed.
Section VO. Context {imgk : img}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfxsegs B.
Variables (ly : alayout) (S : astate) (W : world tfxsegs) (sp0 : Z) (mem0 : word -> option byte) (md0 : Model).
Variable mut : Z -> Prop.
Hypothesis Hmut_img : forall a, mut a -> img_byte_ok tfxsegs a = true.
Hypothesis Hmut_dec : forall a, mut a \/ ~ mut a.
Hypothesis HFown : forall a, mut a -> ~ aowned B ly S a.
Hypothesis Hstk : ly_stk_lo ly + VF_STK <= sp0.
Hypothesis Htop : sp0 <= ly_stk_hi ly.
Definition VO (mem : word -> option byte) (md : Model) : Prop :=
AR tfxsegs B ly S W mem md /\ same_but_materialized md0 md /\
(forall a, vf_band sp0 a -> apresent (w_H W) mem a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_band sp0 a -> ~ mut a -> aview tfxsegs (w_H W) mem a = aview tfxsegs (w_H W) mem0 a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ mut a -> apresent (w_H W) mem0 a -> apresent (w_H W) mem a).
Lemma VO_init : AR tfxsegs B ly S W mem0 md0 -> (forall a, vf_band sp0 a -> apresent (w_H W) mem0 a) -> VO mem0 md0.
Proof.
intros HAR Hp. split; [img_try (img_exact HAR)|]. split; [img_try (img_apply same_but_materialized_refl)|]. split; [img_try (img_exact Hp)|].
split; [img_try (intros; img_refl) | img_try (intros a _ _ Ha; img_exact Ha)].
Qed.
Lemma VO_run : forall mem md memB mat,
VO mem md ->
(forall x : word, ~ vf_band sp0 (bv_unsigned x) -> ~ mut (bv_unsigned x) -> memB x = mem x) ->
(forall x : word, ~ vf_band sp0 (bv_unsigned x) -> ~ mut (bv_unsigned x) -> mrestrict (w_H W) memB x = mrestrict (w_H W) mem x) ->
(forall a, vf_band sp0 a -> apresent (w_H W) memB a) ->
VO memB (with_vm_backing (m_vm_lazy md) mat md).
Proof.
intros mem md memB mat (HAR & Hsbm & Hpb & Hfr & Hpm) HF HFr HpbB.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (HVF : VF_STK = 9104) by img_refl.
assert (AVB : forall a, 0 <= a < 2 ^ 64 -> ~ vf_band sp0 a -> ~ mut a -> aview tfxsegs (w_H W) memB a = aview tfxsegs (w_H W) mem a).
{ intros a Hr H1 H2. img_apply aview_eq_of. img_apply HFr; rewrite unsigned_lit_small by img_lia; assumption. }
pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat)) as MF.
split; [|img_try (split; [|split; [img_exact HpbB | split]])].
- img_apply (al_frame _ _ LAWS ly S W mem md memB _ HAR).
+ intros a Hr Hown. img_apply AVB; [img_try (img_exact Hr) | |].
* intros Hb. img_exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(img_try (unfold vf_band in Hb; img_lia)) Hown).
* intros Hf. img_exact (HFown a Hf Hown).
+ assert (PV : forall a, 0 <= a < 2 ^ 64 -> aview tfxsegs (w_H W) mem a <> None -> aview tfxsegs (w_H W) memB a <> None).
{ intros a Hr Hv.
assert (CASE : vf_band sp0 a \/ mut a \/ (~ vf_band sp0 a /\ ~ mut a)).
{ destruct (Hmut_dec a) as [Hm|Hm]; [img_try (right; left; img_exact Hm)|]. assert (D : vf_band sp0 a \/ ~ vf_band sp0 a) by (img_try (unfold vf_band; img_lia)). tauto. }
destruct CASE as [Hin | [Hin | [Ho1 Ho2]]].
* img_apply aview_some_of_apresent. img_apply HpbB. img_exact Hin.
*
unfold aview, mbyte. destruct (mrestrict (w_H W) memB (Z_to_bv 64 a)) as [b|]; [img_try (cbn; discriminate)|].
pose proof (Hmut_img a Hin) as Hb.
unfold img_byte_ok, img_byte in Hb. destruct (seg_rom tfxsegs (Z_to_bv 64 a)); [img_try (cbn; discriminate) | img_try (discriminate Hb)].
* rewrite AVB; assumption. }
intros a Hv. rewrite (aview_mod _ memB a). img_apply PV; [img_try (img_apply Z.mod_pos_bound; img_lia) | img_try (rewrite <- aview_mod; img_exact Hv)].
+ img_apply MF. + img_apply MF. + img_apply MF.
+
intros a Ha Hh. unfold YG0d.w64 in Hh. unfold YG0d.w64.     destruct (Hmut_dec a) as [Hmt|Hmt].
* exfalso. pose proof (Hmut_img a Hmt) as Hb. unfold img_byte_ok, img_byte in Hb. rewrite (seg_rom_none_band a Ha) in Hb. discriminate Hb.
* assert (CASE : vf_band sp0 a \/ ~ vf_band sp0 a) by (img_try (unfold vf_band; img_lia)).
destruct CASE as [Hin|Hout]; [img_try (exfalso; destruct (Hpb a Hin) as [Hf _]; rewrite Hf in Hh; discriminate Hh)|].
rewrite HF; [img_refl | |]; rewrite unsigned_lit_small by (img_try (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; img_lia)); assumption.
- eapply same_but_materialized_trans; [img_try (img_exact Hsbm) | img_try (img_apply with_vm_backing_same)].
- intros a Hr H1 H2. rewrite AVB by assumption. img_apply Hfr; assumption.
- intros a Hr Hf Hp.
assert (CASE : vf_band sp0 a \/ ~ vf_band sp0 a) by (img_try (unfold vf_band; img_lia)).
destruct CASE as [Hin | Hout]; [img_try (img_apply HpbB; img_exact Hin)|].
destruct (Hpm a Hr Hf Hp) as [Hh [b Hb]]. split; [img_try (img_exact Hh)|]. exists b. rewrite HF; [img_try (img_exact Hb)| |]; rewrite unsigned_lit_small by img_lia; assumption.
Qed.
Lemma VO_splice : forall mem md memB mdB (Sx : Z -> Prop),
VO mem md ->
AR tfxsegs B ly S W memB mdB -> same_but_materialized md mdB ->
(forall a, Sx a -> vf_band sp0 a \/ mut a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Sx a -> aview tfxsegs (w_H W) memB a = aview tfxsegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) memB a) ->
VO memB mdB.
Proof.
intros mem md memB mdB Sx (HAR & Hsbm & Hpb & Hfr & Hpm) HARB HsbmB HSx HfrB HpmB.
split; [img_try (img_exact HARB)|]. split; [img_try (eapply same_but_materialized_trans; [img_exact Hsbm | img_exact HsbmB])|].
split; [img_try (intros a Ha; img_apply HpmB; img_apply Hpb; img_exact Ha)|]. split.
- intros a Hr H1 H2. rewrite HfrB; [img_try (img_apply Hfr; assumption) | img_try (img_exact Hr) | img_try (intros Hs; destruct (HSx a Hs) as [Hb|Hm]; [img_exact (H1 Hb) | img_exact (H2 Hm)])].
- intros a Hr Hf Hp. img_apply HpmB. img_apply Hpm; assumption.
Qed.
End VO.
Lemma vo_shadow_xfer {imgk : img} : forall B ly S (W : world tfxsegs) sp0 mem0 md0 blo bhi mem md x0 m x n,
VO B ly S W sp0 mem0 md0 (vo_mut blo bhi) mem md -> bhi <= STDOUT_BUFA + STDOUT_BSZ -> ly_stk_lo ly + VF_STK <= sp0 ->
range_addressable (aview tfxsegs (w_H W) mem0) SHADOW_OFF x0 m -> shadow_hull_vis (aview tfxsegs (w_H W) mem0) x0 m ->
0 <= x0 -> x0 <= x -> x + n <= x0 + m -> x0 + m <= kHighMemEnd ->
range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview tfxsegs (w_H W) mem) x n).
Proof.
intros B ly S W sp0 mem0 md0 blo bhi mem md x0 m x n (HAR & _ & _ & Hfr & _) Hbhi Hstk Hra Hh Hx0 Hx1 Hx2 Hx3.
assert (HVF : VF_STK = 9104) by img_refl. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (SH : forall y, 0 <= y < kHighMemEnd -> forall s, shadow_addr y / 8 * 8 <= s < shadow_addr y / 8 * 8 + 8 ->
aview tfxsegs (w_H W) mem s = aview tfxsegs (w_H W) mem0 s).
{ intros y Hy s Hs. pose proof (shadow_addr_bounds y Hy) as [B1 B2].
img_apply Hfr; unfold vf_band, vo_mut, vo_file, F_STDOUT, FILE_SZ, STDOUT_BUFA, STDOUT_BSZ in *; unfold kLowMemEnd, kHighShadowEnd, kHighMemBeg in *; img_lia. }
split.
- intros y Hy. destruct (Hra y ltac:(img_lia)) as (v & Hv & Hok). exists v. split; [|img_try (img_exact Hok)].
rewrite (SH y ltac:(img_lia)); [img_try (img_exact Hv)|]. img_change (shadow_of_addr SHADOW_OFF y) with (shadow_addr y). img_lia.
- intros Hn s Hs.
assert (Hy : exists y, x <= y < x + n /\ shadow_addr y / 8 * 8 <= s < shadow_addr y / 8 * 8 + 8).
{ unfold shadow_addr in *.
destruct (Z_lt_le_dec s ((x + n - 1) / 8 + SHADOW_OFF)) as [Hlt|Hge].
+ exists (x + Z.max 0 ((s - SHADOW_OFF) * 8 - x)). split; [img_lia|]. img_lia.
+ exists (x + n - 1). img_lia. }
destruct Hy as (y & Hy1 & Hy2). rewrite (SH y ltac:(img_lia) s Hy2). img_apply Hh. unfold shadow_addr in *. img_lia.
Qed.
Definition vo_rest {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => ((tl (vo_regions []))))).
Lemma vo_rest_ok {imgk : img} : forall E sp0 ap (rest : smem),
skeleton rest = skeleton vo_rest ->
bv_unsigned (ew E 12) = ap -> sp0 <= ap -> ap + 8 <= 2 ^ 47 ->
forall r, In r rest -> (YQ0b.r_base r = None /\ 0 <= YQ0b.r_lo r /\ YQ0b.r_hi r <= 2 ^ 43) \/
(YQ0b.r_base r = Some 12%nat /\ 0 <= YQ0b.r_lo r /\ bv_unsigned (ew E 12) + YQ0b.r_hi r <= 2 ^ 47 /\
sp0 <= bv_unsigned (ew E 12) + YQ0b.r_lo r).
Proof.
intros E sp0 ap rest Hsk H12 Hap1 Hap2 r Hr. pose proof (In_skel rest r Hr) as Hin. rewrite Hsk in Hin.
unfold vo_rest, skeleton in Hin. cbn in Hin. destruct r as [b lo hi wlo whi cs]. unfold skel in Hin. cbn in Hin.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi].
destruct Hin as [Hq|[Hq|[Hq|[Hq|[Hq|[]]]]]]; symmetry in Hq; injection Hq; intros; (subst; cbv beta);
unfold F_STDOUT, FILE_SZ, A_GOT_canary, A_canary, IMG_RO_LO, IMG_RO_HI; first [left; repeat split; img_lia | right; repeat split; img_lia].
Qed.
Lemma vo_rest_w {imgk : img} : forall E (rest : smem), skeleton rest = skeleton vo_rest ->
forall r a (m : word -> option byte), In r rest ->
base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_whi r -> writable_at tfxsegs m a.
Proof.
intros E rest Hsk r a m Hr Ha. pose proof (In_skel rest r Hr) as Hin. rewrite Hsk in Hin.
unfold vo_rest, skeleton in Hin. cbn in Hin. destruct r as [b lo hi wlo whi cs]. unfold skel in Hin. cbn in Hin.
cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Ha.
destruct Hin as [Hq|[Hq|[Hq|[Hq|[Hq|[]]]]]]; symmetry in Hq; injection Hq; intros; (subst; cbv beta); cbn [base_val] in Ha; try img_lia.
unfold F_STDOUT, FILE_SZ in Ha. unfold writable_at.
img_apply (store_ok_all tfxsegs m 232 (Z_to_bv 64 F_STDOUT));
[img_try (rewrite unsigned_lit_small by (unfold F_STDOUT; img_lia); unfold F_STDOUT; cbn; img_lia)
| img_try (img_apply store_ok_wseg; (try img_inst; img_case; vm_compute); img_refl)
| img_try (rewrite !unsigned_lit_small by (unfold F_STDOUT in *; img_lia); unfold F_STDOUT in *; cbn; img_lia)].
Qed.
Lemma vo_rest_disj {imgk : img} : forall E sp0 ap (rest : smem) d n,
skeleton rest = skeleton vo_rest ->
bv_unsigned (ew E 12) = ap -> sp0 <= ap -> 2 ^ 44 <= sp0 ->
STDOUT_BUFA <= d -> d + n <= STDOUT_BUFA + STDOUT_BSZ -> 0 <= n ->
forall r, In r rest -> d + n <= base_val E (YQ0b.r_base r) + YQ0b.r_lo r \/ base_val E (YQ0b.r_base r) + YQ0b.r_hi r <= d.
Proof.
intros E sp0 ap rest d n Hsk H12 Hap Hsp Hd1 Hd2 Hn r Hr. pose proof (In_skel rest r Hr) as Hin. rewrite Hsk in Hin.
unfold vo_rest, skeleton in Hin. cbn in Hin. destruct r as [b lo hi wlo whi cs]. unfold skel in Hin. cbn in Hin.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val].
destruct Hin as [Hq|[Hq|[Hq|[Hq|[Hq|[]]]]]]; symmetry in Hq; injection Hq; intros; (subst; cbv beta); cbn [base_val]; rewrite ?H12;
unfold F_STDOUT, FILE_SZ, A_GOT_canary, A_canary, IMG_RO_LO, IMG_RO_HI, STDOUT_BUFA, STDOUT_BSZ in *; img_lia.
Qed.
Lemma stdout_buf_writable {imgk : img} : forall (m : word -> option byte) a,
STDOUT_BUFA <= a < STDOUT_BUFA + STDOUT_BSZ -> writable_at tfxsegs m a.
Proof.
intros m a Ha. unfold writable_at, STDOUT_BUFA, STDOUT_BSZ in *.
img_apply (store_ok_all tfxsegs m 1024 (Z_to_bv 64 STDOUT_BUFA));
[img_try (rewrite unsigned_lit_small by (unfold STDOUT_BUFA; img_lia); unfold STDOUT_BUFA; cbn; img_lia)
| img_try (img_apply store_ok_wseg; (try img_inst; img_case; vm_compute); img_refl)
| img_try (rewrite !unsigned_lit_small by (unfold STDOUT_BUFA in *; img_lia); unfold STDOUT_BUFA in *; cbn; img_lia)].
Qed.
Definition vo_windows_ok {imgk : img} (ss : sstate) : bool :=
forallb (fun t => band_winb t || win_eqb t (None, F_STDOUT, F_STDOUT + FILE_SZ) || (snd t <=? snd (fst t)))
(windows (ss_mem ss)).
Lemma vo_windows_sound {imgk : img} : forall E ss sp0 a,
vo_windows_ok ss = true -> bv_unsigned (ew E 2) = sp0 ->
in_wrange E (ss_mem ss) a -> vf_band sp0 a \/ vo_file a.
Proof.
intros E ss sp0 a Hb Hsp Hin.
destruct (in_wrange_windows E _ a Hin) as (b & lo & hi & Ht & Hr).
unfold vo_windows_ok in Hb. rewrite forallb_forall in Hb. specialize (Hb _ Ht).
apply orb_prop in Hb as [Hb|Hb]; [img_try (apply orb_prop in Hb as [Hb|Hb])|].
- unfold band_winb in Hb. destruct b as [[|[|[|n]]]|]; try discriminate Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.eqb_eq in H1. apply Z.leb_le in H2. (subst lo; cbv beta).
cbn [base_val] in Hr. rewrite Hsp in Hr. left. unfold vf_band. img_lia.
- apply win_eqb_eq in Hb. injection Hb as -> -> ->. cbn [base_val] in Hr. right. unfold vo_file. img_lia.
- cbn [fst snd] in Hb. apply Z.leb_le in Hb. img_lia.
Qed.
Lemma vo_entry0 {imgk : img} : forall (W : world tfxsegs) regs mem ap cval,
2 ^ 44 <= spZ regs -> spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
(forall a, spZ regs - VF_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 F_STDOUT -> getr regs 11 = w64 FMT_d -> getr regs 12 = w64 ap ->
spZ regs <= ap -> ap + 8 <= 2 ^ 47 -> ap mod 8 = 0 ->
val_mem tfxsegs (mrestrict (w_H W) mem) ap 8 0 ->
stdout_pristine (mrestrict (w_H W) mem) ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
ro_img (mrestrict (w_H W) mem) ->
st_ok tfxsegs (Ereg regs [Z_to_bv 64 0; Z_to_bv 64 cval]) ss_vo0
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_vfprintf) mem (seg_rom tfxsegs))).
Proof.
intros W regs mem ap cval Hsp1 Hsp2 Hal Hpres H10 H11 H12 Hap1 Hap2 Hap8 Harg HF Hgot Hcan Hcv Hro.
rewrite restrict_mkst_fx. unfold ss_vo0.
set (E := Ereg regs [Z_to_bv 64 0; Z_to_bv 64 cval]).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (img_try ((subst E; cbv beta); rewrite (ew_Ereg_nat regs _ 2 2%bv ltac:(img_eqrefl_t)); img_refl)).
assert (E12 : bv_unsigned (ew E 12) = ap) by (img_try ((subst E; cbv beta); rewrite (ew_Ereg_nat regs _ 12 12%bv ltac:(img_eqrefl_t)), H12; img_apply unsigned_lit_small; img_lia)).
assert (E32 : ew E 32 = Z_to_bv 64 0) by (img_try ((subst E; cbv beta); img_exact (ew_Ereg_extra regs _ 0))).
assert (E33 : ew E 33 = Z_to_bv 64 cval) by (img_try ((subst E; cbv beta); img_exact (ew_Ereg_extra regs _ 1))).
assert (HVF : VF_STK = 9104) by img_refl.
img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs [Z_to_bv 64 0; Z_to_bv 64 cval]) with E.
- unfold vo_sr. img_apply regs_ok_pin; [img_try (img_apply regs_ok_pin; [img_apply regs_ok_Ereg | intros Hx; discriminate Hx | rewrite H10; img_refl])
| img_try (intros Hx; discriminate Hx) | img_try (rewrite H11; img_refl)].
- img_case; vm_compute. all: img_refl.
- unfold vo_regions. repeat img_apply Forall_cons; try img_apply Forall_nil.
+ img_apply (region_ok_stack tfxsegs E _ 2 (spZ regs) (- VF_STK)); [img_try (img_exact E2) | img_lia | img_lia |].
intros a Ha. img_apply apresent_writable. img_apply Hpres. img_lia.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
unfold F_STDOUT, FILE_SZ. split; [img_lia|]. split; [img_lia|]. split.
* intros o Ho. rewrite Z.add_0_l. unfold writable_at.
img_apply (store_ok_all tfxsegs (mrestrict (w_H W) mem) 232 (Z_to_bv 64 F_STDOUT));
[img_try (rewrite unsigned_lit_small by (unfold F_STDOUT; img_lia); unfold F_STDOUT; cbn; img_lia)
| img_try (img_apply store_ok_wseg; (try img_inst; img_case; vm_compute); img_refl)
| img_try (rewrite !unsigned_lit_small by (unfold F_STDOUT in *; img_lia); unfold F_STDOUT in *; cbn; img_lia)].
* unfold fo_chunks, stdout_fields0. cbn [map].
unfold stdout_pristine, ofile_is, stdout_fields0 in HF.
repeat match type of HF with Forall _ (_ :: _) =>
let h := fresh "HFf" in pose proof (Forall_inv HF) as h; cbn beta iota in h; apply Forall_inv_tail in HF end.
repeat img_apply Forall_cons; try img_apply Forall_nil;
(eapply (chunk_ok_val tfxsegs E _ 0); [img_refl | img_try (unfold STDOUT_BUFA, STDOUT_BSZ; img_zside) | img_try (img_zside) | img_try (rewrite Z.add_0_l; unfold F_STDOUT, STDOUT_BUFA, STDOUT_BSZ in *; assumption)]).
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
unfold A_GOT_canary. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|].
constructor; [|img_try (constructor)]. eapply (chunk_ok_val tfxsegs E _ 0); [img_refl | img_try (unfold A_canary; img_zside) | img_try (img_zside) |].
rewrite Z.add_0_l. img_exact Hgot.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
unfold A_canary. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|].
constructor; [|img_try (constructor)]. eapply (chunk_ok_val tfxsegs E _ 0 _ 8 _ cval); [| img_try (img_zside) | img_try (img_zside) | img_try (rewrite Z.add_0_l; img_exact Hcan)].
cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite E12. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|].
constructor; [|img_try (constructor)]. eapply (chunk_ok_val tfxsegs E _ ap 0 8 _ 0); [img_refl | img_try (img_zside) | img_try (img_zside) | img_try (rewrite Z.add_0_r; img_exact Harg)].
+ img_apply Hro.
- img_apply pairwise_disjoint_of_extents. unfold vo_regions, img_ro_region, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. rewrite E2, E12.
unfold F_STDOUT, FILE_SZ, A_GOT_canary, A_canary, IMG_RO_LO, IMG_RO_HI.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; img_lia.
- split; [|img_try (split; img_exact I)].
cbn [vo_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2, E12.
img_change (2 ^ 4) with 16. img_change (2 ^ 3) with 8. repeat split; try img_lia.
Qed.
Lemma vo_entry1 {imgk : img} : forall (W : world tfxsegs) regs mem ap cval wp,
2 ^ 44 <= spZ regs -> spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
(forall a, spZ regs - VF_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 F_STDOUT -> getr regs 11 = w64 FMT_d -> getr regs 12 = w64 ap ->
spZ regs <= ap -> ap + 8 <= 2 ^ 47 -> ap mod 8 = 0 ->
val_mem tfxsegs (mrestrict (w_H W) mem) ap 8 0 ->
stdout_mid wp (mrestrict (w_H W) mem) -> STDOUT_BUFA <= wp <= STDOUT_BUFA + STDOUT_BSZ - 2 ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
ro_img (mrestrict (w_H W) mem) ->
st_ok tfxsegs (Ereg regs [Z_to_bv 64 0; Z_to_bv 64 cval; Z_to_bv 64 wp]) ss_vo1
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_vfprintf) mem (seg_rom tfxsegs))).
Proof.
intros W regs mem ap cval wp Hsp1 Hsp2 Hal Hpres H10 H11 H12 Hap1 Hap2 Hap8 Harg [HF Hwp] Hwpr Hgot Hcan Hcv Hro.
rewrite restrict_mkst_fx. unfold ss_vo1.
set (E := Ereg regs [Z_to_bv 64 0; Z_to_bv 64 cval; Z_to_bv 64 wp]).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (img_try ((subst E; cbv beta); rewrite (ew_Ereg_nat regs _ 2 2%bv ltac:(img_eqrefl_t)); img_refl)).
assert (E12 : bv_unsigned (ew E 12) = ap) by (img_try ((subst E; cbv beta); rewrite (ew_Ereg_nat regs _ 12 12%bv ltac:(img_eqrefl_t)), H12; img_apply unsigned_lit_small; img_lia)).
assert (E32 : ew E 32 = Z_to_bv 64 0) by (img_try ((subst E; cbv beta); img_exact (ew_Ereg_extra regs _ 0))).
assert (E33 : ew E 33 = Z_to_bv 64 cval) by (img_try ((subst E; cbv beta); img_exact (ew_Ereg_extra regs _ 1))).
assert (E34 : ew E 34 = Z_to_bv 64 wp) by (img_try ((subst E; cbv beta); img_exact (ew_Ereg_extra regs _ 2))).
assert (HVF : VF_STK = 9104) by img_refl.
img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs [Z_to_bv 64 0; Z_to_bv 64 cval; Z_to_bv 64 wp]) with E.
- unfold vo_sr. img_apply regs_ok_pin; [img_try (img_apply regs_ok_pin; [img_apply regs_ok_Ereg | intros Hx; discriminate Hx | rewrite H10; img_refl])
| img_try (intros Hx; discriminate Hx) | img_try (rewrite H11; img_refl)].
- img_case; vm_compute. all: img_refl.
- unfold vo_regions. repeat img_apply Forall_cons; try img_apply Forall_nil.
+ img_apply (region_ok_stack tfxsegs E _ 2 (spZ regs) (- VF_STK)); [img_try (img_exact E2) | img_lia | img_lia |].
intros a Ha. img_apply apresent_writable. img_apply Hpres. img_lia.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
unfold F_STDOUT, FILE_SZ. split; [img_lia|]. split; [img_lia|]. split.
* intros o Ho. rewrite Z.add_0_l. unfold writable_at.
img_apply (store_ok_all tfxsegs (mrestrict (w_H W) mem) 232 (Z_to_bv 64 F_STDOUT));
[img_try (rewrite unsigned_lit_small by (unfold F_STDOUT; img_lia); unfold F_STDOUT; cbn; img_lia)
| img_try (img_apply store_ok_wseg; (try img_inst; img_case; vm_compute); img_refl)
| img_try (rewrite !unsigned_lit_small by (unfold F_STDOUT in *; img_lia); unfold F_STDOUT in *; cbn; img_lia)].
* unfold fo_chunks, stdout_fields1. cbn [map].
unfold ofile_is, stdout_fields1 in HF.
repeat match type of HF with Forall _ (_ :: _) =>
let h := fresh "HFf" in pose proof (Forall_inv HF) as h; cbn beta iota in h; apply Forall_inv_tail in HF end.
img_apply Forall_cons.
{ eapply (chunk_ok_val tfxsegs E _ 0 _ 8 _ wp); [| img_try (unfold STDOUT_BUFA, STDOUT_BSZ in *; img_zside) | img_try (img_zside) | img_try (rewrite Z.add_0_l; img_exact Hwp)].
cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned. img_refl. }
repeat img_apply Forall_cons; try img_apply Forall_nil;
(eapply (chunk_ok_val tfxsegs E _ 0); [img_refl | img_try (unfold STDOUT_BUFA, STDOUT_BSZ; img_zside) | img_try (img_zside) | img_try (rewrite Z.add_0_l; unfold F_STDOUT, STDOUT_BUFA, STDOUT_BSZ in *; assumption)]).
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
unfold A_GOT_canary. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|].
constructor; [|img_try (constructor)]. eapply (chunk_ok_val tfxsegs E _ 0); [img_refl | img_try (unfold A_canary; img_zside) | img_try (img_zside) |].
rewrite Z.add_0_l. img_exact Hgot.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
unfold A_canary. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|].
constructor; [|img_try (constructor)]. eapply (chunk_ok_val tfxsegs E _ 0 _ 8 _ cval); [| img_try (img_zside) | img_try (img_zside) | img_try (rewrite Z.add_0_l; img_exact Hcan)].
cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite E12. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|].
constructor; [|img_try (constructor)]. eapply (chunk_ok_val tfxsegs E _ ap 0 8 _ 0); [img_refl | img_try (img_zside) | img_try (img_zside) | img_try (rewrite Z.add_0_r; img_exact Harg)].
+ img_apply Hro.
- img_apply pairwise_disjoint_of_extents. unfold vo_regions, img_ro_region, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. rewrite E2, E12.
unfold F_STDOUT, FILE_SZ, A_GOT_canary, A_canary, IMG_RO_LO, IMG_RO_HI.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; img_lia.
- split; [|img_try (split; img_exact I)].
cbn [vo_facts1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2, E12, E34, unsigned_lit_small by (img_try (unfold STDOUT_BUFA, STDOUT_BSZ in *; img_lia)).
img_change (2 ^ 4) with 16. img_change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r. repeat split; try img_lia.
Qed.
Lemma srz_sym_ioctl_enotty {imgk : img} : forall (W : world tfxsegs) E ss ms model fd ch T,
AI tfxsegs (w_H W) (w_A W) model ->
st_ok_ecall tfxsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
bv_unsigned (sv_denot E (sr_get (ss_regs ss) 17)) = 29 ->
sv_denot E (sr_get (ss_regs ss) 10) = fd -> fdchan fd ch model -> fd32 fd = fd ->
cmd32 (sv_denot E (sr_get (ss_regs ss) 11)) = TIOCGWINSZ ->
(forall ms', st_ok tfxsegs E (resume ss (SLit (2 ^ 64 - 25)) (ss_mem ss) (ss_facts ss)) (restrict (w_H W) ms') ->
ms_mem ms' = ms_mem ms -> srealizes tfxsegs (mkCfg ms' model) T) ->
srealizes tfxsegs (mkCfg ms model) T.
Proof.
intros W E ss ms model fd ch T HAI HS Hrv H17 H10 [Hlk _] H32 H11 Hk.
destruct (st_ok_ecall_shape_r tfxsegs (w_H W) E ss ms HS Hrv) as (regs & mem & -> & Hregs & Hmem & HG).
cbn [ms_mem pend_at] in Hk.
eapply (srz_ioctl_winsz_lazy tfxsegs (w_H W) (w_A W) regs _ mem (seg_rom tfxsegs) model fd _ T HAI).
- rewrite (Hregs 17%bv). img_exact H17.
- rewrite (Hregs 10%bv). img_exact H10.
- img_exact H32.
- img_exact Hlk.
- intros rd wr; discriminate.
- rewrite (Hregs 11%bv). img_exact H11.
- apply (Hk (mkst (regupd regs 10 (errno_ret ENOTTY)) (v_addi (Z_to_bv 64 (ss_pc ss)) 4) mem (seg_rom tfxsegs))); [|img_refl].
rewrite restrict_mkst_fx.
replace (errno_ret ENOTTY) with (sv_denot E (SLit (2 ^ 64 - 25))) by (img_try (img_apply bv_eq; (try img_inst; img_case; vm_compute); img_refl)).
img_apply st_ok_resume_sv; auto.
Qed.
Definition o_st1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL ss_vo0)))).
Definition o_af1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt 34 o_st1 RA_FX OSP_FX 0 []))).
Definition o_st2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL o_af1)))).
Definition o_af2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt 50 o_st2 RA_FX OSP_FX 0 []))).
Definition o_st3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL o_af2)))).
Definition o_af3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt 66 o_st3 RA_PAD OSP_PC PAD_OFF (repeat 48 1%nat)))).
Definition o_st4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL o_af3)))).
Definition o_af4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt 82 o_st4 RA_FX OSP_FX 0 []))).
Definition o_st5 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL o_af4)))).
Definition o_af5 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt 98 o_st5 RA_FX OSP_FX 0 []))).
Definition o_st6 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL o_af5)))).
Definition o_af6 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (resume o_st6 (SLit (2 ^ 64 - 25)) (ss_mem o_st6) (ss_facts o_st6)))).
Definition o_st7 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL o_af6)))).
Definition o_af7 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (wl_after o_st7 0 (-1120) 114))).
Definition o_st8 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL o_af7)))).
Definition o_af8 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt 125 o_st8 RA_FX OSP_FX 0 []))).
Definition o_st9 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL o_af8)))).
Definition o_r01 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem o_st1)))).
Definition o_rest1 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem o_st1)))).
Definition o_r02 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem o_st2)))).
Definition o_rest2 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem o_st2)))).
Definition o_r03 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem o_st3)))).
Definition o_rest3 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem o_st3)))).
Definition o_r04 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem o_st4)))).
Definition o_rest4 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem o_st4)))).
Definition o_r05 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem o_st5)))).
Definition o_rest5 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem o_st5)))).
Definition o_r08 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem o_st8)))).
Definition o_rest8 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem o_st8)))).
Lemma o_run1 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL ss_vo0 = (o_st1, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma o_run2 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL o_af1 = (o_st2, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma o_run3 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL o_af2 = (o_st3, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma o_run4 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL o_af3 = (o_st4, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma o_run5 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL o_af4 = (o_st5, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma o_run6 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL o_af5 = (o_st6, RS_ecall). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma o_run7 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL o_af6 = (o_st7, RS_ecall). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma o_run8 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL o_af7 = (o_st8, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma o_run9 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL o_af8 = (o_st9, RS_stopped (SR_jalr (SOff 1 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition BUFEND {imgk : img} : Z := STDOUT_BUFA + STDOUT_BSZ.
Definition fx_cond {imgk : img} (d l : Z) : acond := mkAC BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (d - BUFEND))) (SLit l).
Definition n_st1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL ss_vo1)))).
Definition n_st1c {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (YQ09.add_cond n_st1 (fx_cond 0 0)))).
Definition n_st2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL n_st1c)))).
Definition n_af2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt 35 n_st2 RA_FX OSP_FX 0 []))).
Definition n_st3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL n_af2)))).
Definition n_af3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt 51 n_st3 RA_FX OSP_FX 0 []))).
Definition n_st4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL n_af3)))).
Definition n_af4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt 67 n_st4 RA_PAD OSP_PC PAD_OFF (repeat 48 1%nat)))).
Definition n_st5 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL n_af4)))).
Definition n_st5c {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (YQ09.add_cond n_st5 (fx_cond 0 1)))).
Definition n_st6 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL n_st5c)))).
Definition n_af6 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt 83 n_st6 RA_FX OSP_FX 0 []))).
Definition n_st7 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL n_af6)))).
Definition n_st7c {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (YQ09.add_cond n_st7 (fx_cond 1 0)))).
Definition n_st8 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL n_st7c)))).
Definition n_af8 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt 99 n_st8 RA_FX OSP_FX 0 []))).
Definition n_st9 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL n_af8)))).
Definition n_st9c {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (YQ09.add_cond n_st9 (fx_cond 1 1)))).
Definition n_st10 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL n_st9c)))).
Definition n_af10 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt 115 n_st10 RA_FX OSP_FX 0 []))).
Definition n_st11 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL n_af10)))).
Definition n_r02 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem n_st2)))).
Definition n_rest2 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem n_st2)))).
Definition n_r03 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem n_st3)))).
Definition n_rest3 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem n_st3)))).
Definition n_r04 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem n_st4)))).
Definition n_rest4 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem n_st4)))).
Definition n_r06 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem n_st6)))).
Definition n_rest6 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem n_st6)))).
Definition n_r08 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem n_st8)))).
Definition n_rest8 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem n_st8)))).
Definition n_r010 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem n_st10)))).
Definition n_rest10 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem n_st10)))).
Lemma n_run1 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL ss_vo1 = (n_st1, RS_stopped (SR_branch BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (0 - BUFEND))) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma n_run2 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL n_st1c = (n_st2, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma n_run3 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL n_af2 = (n_st3, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma n_run4 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL n_af3 = (n_st4, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma n_run5 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL n_af4 = (n_st5, RS_stopped (SR_branch BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (0 - BUFEND))) (SLit 1))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma n_run6 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL n_st5c = (n_st6, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma n_run7 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL n_af6 = (n_st7, RS_stopped (SR_branch BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (1 - BUFEND))) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma n_run8 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL n_st7c = (n_st8, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma n_run9 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL n_af8 = (n_st9, RS_stopped (SR_branch BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (1 - BUFEND))) (SLit 1))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma n_run10 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL n_st9c = (n_st10, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma n_run11 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL n_af10 = (n_st11, RS_stopped (SR_jalr (SOff 1 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition find_chunk8 (rs : smem) (i : nat) (off : Z) : option sv :=
match nth_error rs i with
| Some r => match YQ0b.r_base r with
| None => match List.find (fun c => YQ0b.c_off c =? off) (YQ0b.r_chunks r) with
| Some (YQ0b.mkChunk _ (CVal n e)) => if (n =? 8)%N then Some e else None
| _ => None
end
| Some _ => None
end
| None => None
end.
Lemma val_mem_of_chunk8 {imgk : img} : forall E (m : word -> option byte) (rs : smem) i off e v,
mem_ok tfxsegs E m rs -> find_chunk8 rs i off = Some e ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
val_mem tfxsegs m off 8 v.
Proof.
intros E m rs i off e v (Hwf & Hrs & Hpd) Hf He Hv. unfold find_chunk8 in Hf.
destruct (nth_error rs i) as [r|] eqn:Hi; [|img_try (discriminate)].
destruct (YQ0b.r_base r) as [b|] eqn:Hb; [img_try (discriminate)|].
destruct (List.find (fun c => YQ0b.c_off c =? off) (YQ0b.r_chunks r)) as [[co cv]|] eqn:Hfd; [|img_try (discriminate)].
destruct cv as [n e'| | |]; try discriminate. destruct (N.eqb_spec n 8) as [->|Hn]; [|img_try (discriminate)].
injection Hf as ->.
apply find_some in Hfd as [Hin Hoff]. apply Z.eqb_eq in Hoff. cbn [YQ0b.c_off] in Hoff. (subst co; cbv beta).
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. rewrite Hb in Hck. cbn [base_val] in Hck.
rewrite <- (Z.add_0_l off). img_apply (val_of_chunk_ok tfxsegs E m 0 off 8 e v Hck He); cbn; img_lia.
Qed.
Local Ltac GEO := unfold FMT_d, PAD_OFF, OSP_FX, OSP_PC, RA_FX, STDOUT_BUFA, STDOUT_BSZ, F_STDOUT, FILE_SZ, BUFEND in *; img_lia.
Section S. Context {imgk : img}.
Variable B : asyms.
Hypothesis TL : TfxSyms B.
Hypothesis LAWS : AR_laws tfxsegs B.
Hypothesis AMEMCPY : aintrin_realizes tfxsegs B OCpy (pc_wrap_memcpy (as_code B)).
Hypothesis AMEMSET : aintrin_realizes tfxsegs B OSet (pc_wrap_memset (as_code B)).
Let HBcode := ts_code B TL.
Theorem tfx_vfprintf_stdout_first : forall ly S (W : world tfxsegs) regs mem md ch ap cval T,
ecall_pre tfxsegs B ly S W regs mem md ->
2 ^ 44 <= spZ regs -> ly_stk_lo ly + VF_STK <= spZ regs ->
(forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) ->
getr regs 10 = w64 F_STDOUT -> getr regs 11 = w64 FMT_d -> getr regs 12 = w64 ap ->
spZ regs <= ap -> ap + 8 <= 2 ^ 47 -> ap mod 8 = 0 ->
val_mem tfxsegs (mrestrict (w_H W) mem) ap 8 0 ->
stdout_pristine (mrestrict (w_H W) mem) ->
(forall a, vo_file a \/ STDOUT_BUFA <= a < STDOUT_BUFA + STDOUT_BSZ -> ~ aowned B ly S a) ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
ro_img (mrestrict (w_H W) mem) ->
range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF STDOUT_BUFA STDOUT_BSZ ->
shadow_hull_vis (aview tfxsegs (w_H W) mem) STDOUT_BUFA STDOUT_BSZ ->
fdchan (Z_to_bv 64 1) ch md -> AI tfxsegs (w_H W) (w_A W) md ->
(forall regs' mem' md',
AR tfxsegs B ly S W mem' md' -> aregs_preserved regs regs' -> same_but_materialized md md' ->
getr regs' 10 = w64 2 ->
stdout_mid STDOUT_BUFA (mrestrict (w_H W) mem') ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_band (spZ regs) a -> ~ vo_mut STDOUT_BUFA (STDOUT_BUFA + 1) a ->
aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vo_mut STDOUT_BUFA (STDOUT_BUFA + 1) a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
AI tfxsegs (w_H W) (w_A W) md' ->
srealizes tfxsegs (cfg_at tfxsegs (raZ regs) regs' mem' md') T) ->
srealizes tfxsegs (cfg_at tfxsegs A_vfprintf regs mem md) (t_emit (map (WriteEv ch) (map (Z_to_bv 8) [48; 10])) T).
Proof.
intros ly S W regs mem md ch ap cval T HPRE Hsp44 Hstk Hpres Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg
HFP HBown Hgot Hcan Hcv Hro Hra_b Hhull_b Hch HAI0 HK.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by img_refl. assert (HVF : VF_STK = 9104) by img_refl.
assert (HFF : F_STDOUT = (682048 + D_10f0)) by img_refl. assert (HFS : FILE_SZ = 232) by img_refl.
assert (HBF : STDOUT_BUFA = (6281312 + D_10c0)) by img_refl. assert (HBS : STDOUT_BSZ = 1024) by img_refl.
assert (HFD : FMT_d = (84065 + D_20)) by img_refl. assert (HPO : PAD_OFF = -736) by img_refl. assert (HOX : OSP_FX = -976) by img_refl.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by img_refl.
set (sp0 := spZ regs) in *. assert (HtopS : sp0 < kHighMemEnd) by (img_try (rewrite KHI; img_lia)).
assert (Hsp47 : sp0 <= 2 ^ 47) by img_lia.
set (MUT := vo_mut STDOUT_BUFA (STDOUT_BUFA + 1)) in *.
assert (MUTimg : forall a, MUT a -> img_byte_ok tfxsegs a = true) by (img_try (intros a Ha; img_apply (vo_mut_img STDOUT_BUFA (STDOUT_BUFA + 1) a); [img_lia | img_try (unfold STDOUT_BSZ; img_lia) | img_try (img_exact Ha)])).
assert (MUTdec : forall a, MUT a \/ ~ MUT a) by (img_try (intros a; img_apply vo_mut_dec)).
assert (HFownM : forall a, MUT a -> ~ aowned B ly S a) by (img_try (intros a [Ha|Ha]; img_apply HBown; [img_try (left; img_exact Ha) | img_try (right; unfold STDOUT_BSZ; img_lia)])).
unfold cfg_at. img_change (w64 A_vfprintf) with (Z_to_bv 64 A_vfprintf).
pose proof (vo_entry0 W regs mem ap cval Hsp44 Hsp47 Hal16 ltac:(img_try (intros a Ha; img_apply Hpres; img_exact Ha)) Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg
HFP Hgot Hcan Hcv Hro) as HS0.
set (EL := [Z_to_bv 64 0; Z_to_bv 64 cval]) in *.
remember (Ereg regs EL) as E0 eqn:HE0.
assert (EE : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E0 i = getr regs r)
by (img_try (intros i r Hi; rewrite HE0; img_exact (ew_Ereg_nat regs _ i r Hi))).
pose proof (EE 1%nat (1%bv : bv 5) ltac:(img_eqrefl_t)) as E0_1.
assert (Usp0 : bv_unsigned (ew E0 2) = sp0) by (img_try (rewrite (EE 2%nat (2%bv : bv 5) ltac:(img_eqrefl_t)); img_refl)).
assert (G3_0 : ew E0 3 = w64 (as_gp B)) by (img_try (rewrite (EE 3%nat (3%bv : bv 5) ltac:(img_eqrefl_t)); img_exact Hgp)).
assert (G4_0 : ew E0 4 = w64 (as_tp B)) by (img_try (rewrite (EE 4%nat (4%bv : bv 5) ltac:(img_eqrefl_t)); img_exact Htp)).
assert (G12_0 : bv_unsigned (ew E0 12) = ap) by (img_try (rewrite (EE 12%nat (12%bv : bv 5) ltac:(img_eqrefl_t)), Ha2; img_apply unsigned_lit_small; img_lia)).
assert (HAE0 : env_agree 32 (Ereg regs EL) E0) by (img_try (rewrite HE0; split; [img_try (intros i Hi; img_refl) | img_refl])).
set (EA := Ereg regs EL) in *.
clear HE0 EE.
pose proof (VO_init B ly S W sp0 mem md MUT HAR Hpres) as VO0.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E0 ss_vo0 o_st1 _ _ _ HS0 o_run1) HAI0).
intros W1 c1 _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [cfg_model] in HAI1. clear HS0.
rewrite ?wvb_wvb in HAI1 |- *.
assert (VO1 : VO B ly S W sp0 mem md MUT (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms1) mat1 VO0) as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF1. intros Hin. destruct (vo_windows_sound E0 ss_vo0 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- intros x Hx1 Hx2. img_apply HFr1. intros Hin. destruct (vo_windows_sound E0 ss_vo0 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- img_apply (vf_band_present W E0 o_st1 ms1 sp0 HS1 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 ltac:(img_lia)). }
clear VO0 HF1 HFr1.
assert (SRA1' : range_addressable (aview tfxsegs (w_H W) (ms_mem ms1)) SHADOW_OFF FMT_d 0) by (img_try (intros y Hy; img_lia)).
assert (SHU1' : 0 < 0 -> shadow_hull_vis (aview tfxsegs (w_H W) (ms_mem ms1)) FMT_d 0) by (img_try (intros H0; img_lia)).
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_memcpy_ext B LAWS AMEMCPY W E0 o_st1 ms1 _ ly S sp0 o_r01 o_rest1 34 RA_FX OSP_FX
(SLit STDOUT_BUFA) (SLit FMT_d) (SLit 0) (STDOUT_BUFA) (FMT_d) 0
HS1 ltac:(img_try (rewrite HBcode; img_refl)) ltac:(img_eqrefl_t) Usp0 G3_0 G4_0 ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t)
ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t)
ltac:(img_eqrefl_t) ltac:(img_refl) ltac:(img_eqrefl_t) ltac:(img_refl) ltac:(img_eqrefl_t) ltac:(img_refl)
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_lia)
ltac:(img_try (unfold RA_FX; img_lia)) ltac:(img_refl)
ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_try (GEO))
ltac:(img_try (left; unfold kLowMemEnd; GEO))
ltac:(img_try (first [left; unfold kLowMemEnd; GEO | eapply (vf_stack_amem B); [img_try (img_exact (proj1 VO1)) | img_try (img_exact Hstk) | img_try (img_exact HtopS) | img_try (GEO) | img_try (GEO)]]))
(vo_rest_disj E0 sp0 ap o_rest1 (STDOUT_BUFA) 0 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_0 Hap1 Hsp44 ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_lia))
(vo_rest_ok E0 sp0 ap o_rest1 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_0 Hap1 Hap2)
(vo_rest_w E0 o_rest1 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VO1) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VO1)))
ltac:(img_try (intros a Ha; img_lia)) SRA1' SHU1'
ltac:(img_try (intros a Ha; img_lia)) ltac:(img_try (intros y Hy; img_lia)) ltac:(img_try (intros H0; img_lia))) HAI1).
intros W1' c1' _ HAI1' (-> & ms1' & mat1' & -> & HS1' & HAR1' & HP1' & Heff1' & Hfr1' & Hpm1'). cbn [cfg_model] in HAI1'.
rewrite wvb_wvb in HAI1', HAR1' |- *.
img_change (vf_after_icpt 34 o_st1 RA_FX OSP_FX 0 []) with o_af1 in HS1'.
assert (VO1' : VO B ly S W sp0 mem md MUT (ms_mem ms1') (with_vm_backing (m_vm_lazy md) mat1' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms1) _ (ms_mem ms1') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ ((STDOUT_BUFA) <= a < (STDOUT_BUFA) + 0))).
- img_exact VO1.
- img_exact HAR1'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat1' mat1 md). img_apply with_vm_backing_same.
- intros a [Ha|Ha]; [img_try (left; unfold vf_band, OSP_FX in *; img_lia) | img_try (right; unfold MUT, vo_mut; GEO)].
- intros a Hr Hna. img_apply Hfr1'; [img_try (img_exact Hr) | img_try (intros H'; img_apply Hna; left; img_exact H') | img_try (intros H'; img_apply Hna; right; img_exact H')].
- img_exact Hpm1'. }
remember (havoc E0 34 (map (getr (ms_regs ms1')) CLOB)) as E1 eqn:HE1.
assert (OLD1 : forall j, (j < 34)%nat -> ew E1 j = ew E0 j) by (img_try (intros j Hj; rewrite HE1; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp1 : bv_unsigned (ew E1 2) = sp0) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact Usp0)).
assert (G3_1 : ew E1 3 = w64 (as_gp B)) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact G3_0)).
assert (G4_1 : ew E1 4 = w64 (as_tp B)) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact G4_0)).
assert (G12_1 : bv_unsigned (ew E1 12) = ap) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact G12_0)).
assert (HAE1 : env_agree 32 EA E1)
by (img_try (rewrite HE1; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (img_exact HAE0)])).
clear HE1 HS1 VO1 SRA1' SHU1' Heff1'.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E1 o_af1 o_st2 _ _ _ HS1' o_run2) HAI1').
intros W2 c2 _ HAI2 (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). cbn [cfg_model] in HAI2. clear HS1'.
rewrite ?wvb_wvb in HAI2 |- *.
assert (VO2 : VO B ly S W sp0 mem md MUT (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms2) mat2 VO1') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF2. intros Hin. destruct (vo_windows_sound E1 o_af1 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp1 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- intros x Hx1 Hx2. img_apply HFr2. intros Hin. destruct (vo_windows_sound E1 o_af1 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp1 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- img_apply (vf_band_present W E1 o_st2 ms2 sp0 HS2 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp1 ltac:(img_lia)). }
clear VO1' HF2 HFr2.
assert (SRA2' : range_addressable (aview tfxsegs (w_H W) (ms_mem ms2)) SHADOW_OFF (68452 + D_20) 0) by (img_try (intros y Hy; img_lia)).
assert (SHU2' : 0 < 0 -> shadow_hull_vis (aview tfxsegs (w_H W) (ms_mem ms2)) (68452 + D_20) 0) by (img_try (intros H0; img_lia)).
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_memcpy_ext B LAWS AMEMCPY W E1 o_st2 ms2 _ ly S sp0 o_r02 o_rest2 50 RA_FX OSP_FX
(SLit STDOUT_BUFA) (SLit (68452 + D_20)) (SLit 0) (STDOUT_BUFA) ((68452 + D_20)) 0
HS2 ltac:(img_try (rewrite HBcode; img_refl)) ltac:(img_eqrefl_t) Usp1 G3_1 G4_1 ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t)
ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t)
ltac:(img_eqrefl_t) ltac:(img_refl) ltac:(img_eqrefl_t) ltac:(img_refl) ltac:(img_eqrefl_t) ltac:(img_refl)
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_lia)
ltac:(img_try (unfold RA_FX; img_lia)) ltac:(img_refl)
ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_try (GEO))
ltac:(img_try (left; unfold kLowMemEnd; GEO))
ltac:(img_try (first [left; unfold kLowMemEnd; GEO | eapply (vf_stack_amem B); [img_try (img_exact (proj1 VO2)) | img_try (img_exact Hstk) | img_try (img_exact HtopS) | img_try (GEO) | img_try (GEO)]]))
(vo_rest_disj E1 sp0 ap o_rest2 (STDOUT_BUFA) 0 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_1 Hap1 Hsp44 ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_lia))
(vo_rest_ok E1 sp0 ap o_rest2 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_1 Hap1 Hap2)
(vo_rest_w E1 o_rest2 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VO2) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VO2)))
ltac:(img_try (intros a Ha; img_lia)) SRA2' SHU2'
ltac:(img_try (intros a Ha; img_lia)) ltac:(img_try (intros y Hy; img_lia)) ltac:(img_try (intros H0; img_lia))) HAI2).
intros W2' c2' _ HAI2' (-> & ms2' & mat2' & -> & HS2' & HAR2' & HP2' & Heff2' & Hfr2' & Hpm2'). cbn [cfg_model] in HAI2'.
rewrite wvb_wvb in HAI2', HAR2' |- *.
img_change (vf_after_icpt 50 o_st2 RA_FX OSP_FX 0 []) with o_af2 in HS2'.
assert (VO2' : VO B ly S W sp0 mem md MUT (ms_mem ms2') (with_vm_backing (m_vm_lazy md) mat2' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms2) _ (ms_mem ms2') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ ((STDOUT_BUFA) <= a < (STDOUT_BUFA) + 0))).
- img_exact VO2.
- img_exact HAR2'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat2' mat2 md). img_apply with_vm_backing_same.
- intros a [Ha|Ha]; [img_try (left; unfold vf_band, OSP_FX in *; img_lia) | img_try (right; unfold MUT, vo_mut; GEO)].
- intros a Hr Hna. img_apply Hfr2'; [img_try (img_exact Hr) | img_try (intros H'; img_apply Hna; left; img_exact H') | img_try (intros H'; img_apply Hna; right; img_exact H')].
- img_exact Hpm2'. }
remember (havoc E1 50 (map (getr (ms_regs ms2')) CLOB)) as E2 eqn:HE2.
assert (OLD2 : forall j, (j < 50)%nat -> ew E2 j = ew E1 j) by (img_try (intros j Hj; rewrite HE2; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp2 : bv_unsigned (ew E2 2) = sp0) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact Usp1)).
assert (G3_2 : ew E2 3 = w64 (as_gp B)) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact G3_1)).
assert (G4_2 : ew E2 4 = w64 (as_tp B)) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact G4_1)).
assert (G12_2 : bv_unsigned (ew E2 12) = ap) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact G12_1)).
assert (HAE2 : env_agree 32 EA E2)
by (img_try (rewrite HE2; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (img_exact HAE1)])).
clear HE2 HS2 VO2 SRA2' SHU2' Heff2'.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E2 o_af2 o_st3 _ _ _ HS2' o_run3) HAI2').
intros W3 c3 _ HAI3 (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). cbn [cfg_model] in HAI3. clear HS2'.
rewrite ?wvb_wvb in HAI3 |- *.
assert (VO3 : VO B ly S W sp0 mem md MUT (ms_mem ms3) (with_vm_backing (m_vm_lazy md) mat3 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms3) mat3 VO2') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF3. intros Hin. destruct (vo_windows_sound E2 o_af2 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp2 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- intros x Hx1 Hx2. img_apply HFr3. intros Hin. destruct (vo_windows_sound E2 o_af2 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp2 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- img_apply (vf_band_present W E2 o_st3 ms3 sp0 HS3 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp2 ltac:(img_lia)). }
clear VO2' HF3 HFr3.
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_memset B LAWS AMEMSET W E2 o_st3 ms3 _ ly S sp0 o_r03 o_rest3 66 RA_PAD OSP_PC PAD_OFF 48 1%nat
HS3 ltac:(img_try (rewrite HBcode; img_refl)) ltac:(img_eqrefl_t) Usp2 G3_2 G4_2 ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t)
ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_lia) ltac:(img_refl)
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_PC; img_lia)) ltac:(img_try (unfold OSP_PC, PAD_OFF; img_lia)) ltac:(img_try (unfold PAD_OFF; cbn; img_lia)) ltac:(img_try (unfold RA_PAD; img_lia)) ltac:(img_refl)
(vo_rest_ok E2 sp0 ap o_rest3 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_2 Hap1 Hap2)
(vo_rest_w E2 o_rest3 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VO3) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VO3)))) HAI3).
intros W3' c3' _ HAI3' (-> & ms3' & mat3' & -> & HS3' & HAR3' & HP3' & Hfr3' & Hpm3'). cbn [cfg_model] in HAI3'.
rewrite wvb_wvb in HAI3', HAR3' |- *.
img_change (vf_after_icpt 66 o_st3 RA_PAD OSP_PC PAD_OFF (repeat 48 1%nat)) with o_af3 in HS3'.
assert (VO3' : VO B ly S W sp0 mem md MUT (ms_mem ms3') (with_vm_backing (m_vm_lazy md) mat3' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms3) _ (ms_mem ms3') _
(fun a => (sp0 + OSP_PC - ESTACK <= a < sp0 + OSP_PC) \/ (sp0 + PAD_OFF <= a < sp0 + PAD_OFF + 1))).
- img_exact VO3.
- img_exact HAR3'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat3' mat3 md). img_apply with_vm_backing_same.
- intros a Ha. left. unfold vf_band, OSP_PC, PAD_OFF in *. img_lia.
- intros a Hr Hna. img_apply Hfr3'; [img_try (img_exact Hr) | img_try (intros H'; img_apply Hna; left; img_exact H') | img_try (intros H'; img_apply Hna; right; cbn; img_exact H')].
- img_exact Hpm3'. }
remember (havoc E2 66 (map (getr (ms_regs ms3')) CLOB)) as E3 eqn:HE3.
assert (OLD3 : forall j, (j < 66)%nat -> ew E3 j = ew E2 j) by (img_try (intros j Hj; rewrite HE3; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp3 : bv_unsigned (ew E3 2) = sp0) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact Usp2)).
assert (G3_3 : ew E3 3 = w64 (as_gp B)) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact G3_2)).
assert (G4_3 : ew E3 4 = w64 (as_tp B)) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact G4_2)).
assert (G12_3 : bv_unsigned (ew E3 12) = ap) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact G12_2)).
assert (HAE3 : env_agree 32 EA E3)
by (img_try (rewrite HE3; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (img_exact HAE2)])).
clear HE3 HS3 VO3.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E3 o_af3 o_st4 _ _ _ HS3' o_run4) HAI3').
intros W4 c4 _ HAI4 (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). cbn [cfg_model] in HAI4. clear HS3'.
rewrite ?wvb_wvb in HAI4 |- *.
assert (VO4 : VO B ly S W sp0 mem md MUT (ms_mem ms4) (with_vm_backing (m_vm_lazy md) mat4 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms4) mat4 VO3') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF4. intros Hin. destruct (vo_windows_sound E3 o_af3 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp3 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- intros x Hx1 Hx2. img_apply HFr4. intros Hin. destruct (vo_windows_sound E3 o_af3 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp3 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- img_apply (vf_band_present W E3 o_st4 ms4 sp0 HS4 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp3 ltac:(img_lia)). }
clear VO3' HF4 HFr4.
pose proof HS4 as HSc4. destruct HSc4 as (_ & _ & _ & _ & _ & _ & _ & Hmem4 & _). cbn [restrict ms_mem] in Hmem4.
assert (PAD4 : aview tfxsegs (w_H W) (ms_mem ms4) (sp0 + PAD_OFF) = Some 48).
{ replace (sp0 + PAD_OFF) with (sp0 + PAD_OFF + Z.of_nat 0) by img_lia.
img_apply (lit_buf_aview W E3 (ms_mem ms4) (ss_mem o_st4) (SOff 2 PAD_OFF) (sp0 + PAD_OFF) 1 [48] Hmem4 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try (cbn [sv_denot]; rewrite Usp3; img_refl)) ltac:(img_try (repeat constructor; img_lia)) 0%nat ltac:(img_lia)). }
clear Hmem4.
destruct (vf_stack_shadow B LAWS W ly S (ms_mem ms4) _ sp0 (sp0 + PAD_OFF) 1 (proj1 VO4) Hstk Htop ltac:(img_try (unfold PAD_OFF; img_lia)) ltac:(img_try (unfold PAD_OFF; img_lia)) ltac:(img_lia)) as [SRA4' SHU4'].
destruct (vo_shadow_xfer B ly S W sp0 mem md STDOUT_BUFA (STDOUT_BUFA + 1) (ms_mem ms4) _ STDOUT_BUFA STDOUT_BSZ STDOUT_BUFA 1 VO4 ltac:(img_try (unfold STDOUT_BSZ; img_lia)) Hstk Hra_b Hhull_b
ltac:(img_try (unfold STDOUT_BUFA; img_lia)) ltac:(img_lia) ltac:(img_try (unfold STDOUT_BSZ; img_lia)) ltac:(img_try (rewrite KHI; unfold STDOUT_BUFA, STDOUT_BSZ; img_lia))) as [DRA4' DHU4'].
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_memcpy_ext B LAWS AMEMCPY W E3 o_st4 ms4 _ ly S sp0 o_r04 o_rest4 82 RA_FX OSP_FX
(SLit STDOUT_BUFA) (SOff 2 PAD_OFF) (SLit 1) (STDOUT_BUFA) (sp0 + PAD_OFF) 1
HS4 ltac:(img_try (rewrite HBcode; img_refl)) ltac:(img_eqrefl_t) Usp3 G3_3 G4_3 ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t)
ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t)
ltac:(img_eqrefl_t) ltac:(img_refl) ltac:(img_eqrefl_t) ltac:(img_try (cbn [sv_denot]; rewrite Usp3; img_refl)) ltac:(img_eqrefl_t) ltac:(img_refl)
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_lia)
ltac:(img_try (unfold RA_FX; img_lia)) ltac:(img_refl)
ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_try (GEO))
ltac:(img_try (left; unfold kLowMemEnd; GEO))
ltac:(img_try (first [left; unfold kLowMemEnd; GEO | eapply (vf_stack_amem B); [img_try (img_exact (proj1 VO4)) | img_try (img_exact Hstk) | img_try (img_exact HtopS) | img_try (GEO) | img_try (GEO)]]))
(vo_rest_disj E3 sp0 ap o_rest4 (STDOUT_BUFA) 1 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_3 Hap1 Hsp44 ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_lia))
(vo_rest_ok E3 sp0 ap o_rest4 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_3 Hap1 Hap2)
(vo_rest_w E3 o_rest4 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VO4) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VO4)))
ltac:(img_try (intros a Ha; replace a with (sp0 + PAD_OFF) by img_lia; rewrite PAD4; discriminate)) SRA4' SHU4'
ltac:(img_try (intros a Ha; split; [img_try (img_apply stdout_buf_writable; unfold STDOUT_BSZ; img_lia) | img_try (img_apply HBown; right; unfold STDOUT_BSZ; img_lia)])) ltac:(img_try (img_exact DRA4')) ltac:(img_try (img_exact DHU4'))) HAI4).
intros W4' c4' _ HAI4' (-> & ms4' & mat4' & -> & HS4' & HAR4' & HP4' & Heff4' & Hfr4' & Hpm4'). cbn [cfg_model] in HAI4'.
rewrite wvb_wvb in HAI4', HAR4' |- *.
img_change (vf_after_icpt 82 o_st4 RA_FX OSP_FX 0 []) with o_af4 in HS4'.
assert (VO4' : VO B ly S W sp0 mem md MUT (ms_mem ms4') (with_vm_backing (m_vm_lazy md) mat4' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms4) _ (ms_mem ms4') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ ((STDOUT_BUFA) <= a < (STDOUT_BUFA) + 1))).
- img_exact VO4.
- img_exact HAR4'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat4' mat4 md). img_apply with_vm_backing_same.
- intros a [Ha|Ha]; [img_try (left; unfold vf_band, OSP_FX in *; img_lia) | img_try (right; unfold MUT, vo_mut; GEO)].
- intros a Hr Hna. img_apply Hfr4'; [img_try (img_exact Hr) | img_try (intros H'; img_apply Hna; left; img_exact H') | img_try (intros H'; img_apply Hna; right; img_exact H')].
- img_exact Hpm4'. }
assert (BUF04' : aview tfxsegs (w_H W) (ms_mem ms4') (STDOUT_BUFA) = Some 48).
{ rewrite <- PAD4, <- (Z.add_0_r STDOUT_BUFA), <- (Z.add_0_r (sp0 + PAD_OFF)). img_apply (Heff4' 0). img_lia. }
remember (havoc E3 82 (map (getr (ms_regs ms4')) CLOB)) as E4 eqn:HE4.
assert (OLD4 : forall j, (j < 82)%nat -> ew E4 j = ew E3 j) by (img_try (intros j Hj; rewrite HE4; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp4 : bv_unsigned (ew E4 2) = sp0) by (img_try (rewrite OLD4 by ((img_case; cbv); img_lia); img_exact Usp3)).
assert (G3_4 : ew E4 3 = w64 (as_gp B)) by (img_try (rewrite OLD4 by ((img_case; cbv); img_lia); img_exact G3_3)).
assert (G4_4 : ew E4 4 = w64 (as_tp B)) by (img_try (rewrite OLD4 by ((img_case; cbv); img_lia); img_exact G4_3)).
assert (G12_4 : bv_unsigned (ew E4 12) = ap) by (img_try (rewrite OLD4 by ((img_case; cbv); img_lia); img_exact G12_3)).
assert (HAE4 : env_agree 32 EA E4)
by (img_try (rewrite HE4; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (img_exact HAE3)])).
clear HE4 HS4 VO4 SRA4' SHU4' Heff4'.
clear PAD4 DRA4' DHU4'.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E4 o_af4 o_st5 _ _ _ HS4' o_run5) HAI4').
intros W5 c5 _ HAI5 (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). cbn [cfg_model] in HAI5. clear HS4'.
rewrite ?wvb_wvb in HAI5 |- *.
assert (VO5 : VO B ly S W sp0 mem md MUT (ms_mem ms5) (with_vm_backing (m_vm_lazy md) mat5 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms5) mat5 VO4') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF5. intros Hin. destruct (vo_windows_sound E4 o_af4 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp4 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- intros x Hx1 Hx2. img_apply HFr5. intros Hin. destruct (vo_windows_sound E4 o_af4 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp4 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- img_apply (vf_band_present W E4 o_st5 ms5 sp0 HS5 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp4 ltac:(img_lia)). }
assert (BUF05 : aview tfxsegs (w_H W) (ms_mem ms5) (STDOUT_BUFA) = Some 48).
{ rewrite <- BUF04'. img_apply aview_eq_of. img_apply HFr5. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (vo_windows_sound E4 o_af4 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp4 Hin) as [Hw|Hw]; [img_try (unfold vf_band in Hw; GEO) | img_try (unfold vo_file, F_STDOUT, FILE_SZ in Hw; GEO)]. }
clear VO4' HF5 HFr5 BUF04'.
assert (SRA5' : range_addressable (aview tfxsegs (w_H W) (ms_mem ms5)) SHADOW_OFF (sp0 + PAD_OFF) 0) by (img_try (intros y Hy; img_lia)).
assert (SHU5' : 0 < 0 -> shadow_hull_vis (aview tfxsegs (w_H W) (ms_mem ms5)) (sp0 + PAD_OFF) 0) by (img_try (intros H0; img_lia)).
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_memcpy_ext B LAWS AMEMCPY W E4 o_st5 ms5 _ ly S sp0 o_r05 o_rest5 98 RA_FX OSP_FX
(SLit (STDOUT_BUFA + 1)) (SOff 2 PAD_OFF) (SLit 0) (STDOUT_BUFA + 1) (sp0 + PAD_OFF) 0
HS5 ltac:(img_try (rewrite HBcode; img_refl)) ltac:(img_eqrefl_t) Usp4 G3_4 G4_4 ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t)
ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t)
ltac:(img_eqrefl_t) ltac:(img_refl) ltac:(img_eqrefl_t) ltac:(img_try (cbn [sv_denot]; rewrite Usp4; img_refl)) ltac:(img_eqrefl_t) ltac:(img_refl)
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_lia)
ltac:(img_try (unfold RA_FX; img_lia)) ltac:(img_refl)
ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_try (GEO))
ltac:(img_try (left; unfold kLowMemEnd; GEO))
ltac:(img_try (first [left; unfold kLowMemEnd; GEO | eapply (vf_stack_amem B); [img_try (img_exact (proj1 VO5)) | img_try (img_exact Hstk) | img_try (img_exact HtopS) | img_try (GEO) | img_try (GEO)]]))
(vo_rest_disj E4 sp0 ap o_rest5 (STDOUT_BUFA + 1) 0 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_4 Hap1 Hsp44 ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_lia))
(vo_rest_ok E4 sp0 ap o_rest5 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_4 Hap1 Hap2)
(vo_rest_w E4 o_rest5 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VO5) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VO5)))
ltac:(img_try (intros a Ha; img_lia)) SRA5' SHU5'
ltac:(img_try (intros a Ha; img_lia)) ltac:(img_try (intros y Hy; img_lia)) ltac:(img_try (intros H0; img_lia))) HAI5).
intros W5' c5' _ HAI5' (-> & ms5' & mat5' & -> & HS5' & HAR5' & HP5' & Heff5' & Hfr5' & Hpm5'). cbn [cfg_model] in HAI5'.
rewrite wvb_wvb in HAI5', HAR5' |- *.
img_change (vf_after_icpt 98 o_st5 RA_FX OSP_FX 0 []) with o_af5 in HS5'.
assert (VO5' : VO B ly S W sp0 mem md MUT (ms_mem ms5') (with_vm_backing (m_vm_lazy md) mat5' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms5) _ (ms_mem ms5') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ ((STDOUT_BUFA + 1) <= a < (STDOUT_BUFA + 1) + 0))).
- img_exact VO5.
- img_exact HAR5'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat5' mat5 md). img_apply with_vm_backing_same.
- intros a [Ha|Ha]; [img_try (left; unfold vf_band, OSP_FX in *; img_lia) | img_try (right; unfold MUT, vo_mut; GEO)].
- intros a Hr Hna. img_apply Hfr5'; [img_try (img_exact Hr) | img_try (intros H'; img_apply Hna; left; img_exact H') | img_try (intros H'; img_apply Hna; right; img_exact H')].
- img_exact Hpm5'. }
assert (BUF05' : aview tfxsegs (w_H W) (ms_mem ms5') (STDOUT_BUFA) = Some 48).
{ rewrite <- BUF05. img_apply Hfr5'; [img_try (GEO) | img_try (GEO) | img_try (GEO)]. }
remember (havoc E4 98 (map (getr (ms_regs ms5')) CLOB)) as E5 eqn:HE5.
assert (OLD5 : forall j, (j < 98)%nat -> ew E5 j = ew E4 j) by (img_try (intros j Hj; rewrite HE5; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp5 : bv_unsigned (ew E5 2) = sp0) by (img_try (rewrite OLD5 by ((img_case; cbv); img_lia); img_exact Usp4)).
assert (G3_5 : ew E5 3 = w64 (as_gp B)) by (img_try (rewrite OLD5 by ((img_case; cbv); img_lia); img_exact G3_4)).
assert (G4_5 : ew E5 4 = w64 (as_tp B)) by (img_try (rewrite OLD5 by ((img_case; cbv); img_lia); img_exact G4_4)).
assert (G12_5 : bv_unsigned (ew E5 12) = ap) by (img_try (rewrite OLD5 by ((img_case; cbv); img_lia); img_exact G12_4)).
assert (HAE5 : env_agree 32 EA E5)
by (img_try (rewrite HE5; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (img_exact HAE4)])).
clear HE5 HS5 VO5 SRA5' SHU5' Heff5' BUF05.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E5 o_af5 o_st6 _ _ _ HS5' o_run6) HAI5').
intros W6 c6 _ HAI6 (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). cbn [cfg_model] in HAI6. clear HS5'.
rewrite ?wvb_wvb in HAI6 |- *.
assert (VO6 : VO B ly S W sp0 mem md MUT (ms_mem ms6) (with_vm_backing (m_vm_lazy md) mat6 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms6) mat6 VO5') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF6. intros Hin. destruct (vo_windows_sound E5 o_af5 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp5 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- intros x Hx1 Hx2. img_apply HFr6. intros Hin. destruct (vo_windows_sound E5 o_af5 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp5 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- img_apply (vf_band_present_ecall W E5 o_st6 ms6 sp0 HS6 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp5 ltac:(img_lia)). }
assert (BUF06 : aview tfxsegs (w_H W) (ms_mem ms6) (STDOUT_BUFA) = Some 48).
{ rewrite <- BUF05'. img_apply aview_eq_of. img_apply HFr6. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (vo_windows_sound E5 o_af5 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp5 Hin) as [Hw|Hw]; [img_try (unfold vf_band in Hw; GEO) | img_try (unfold vo_file, F_STDOUT, FILE_SZ in Hw; GEO)]. }
clear VO5' HF6 HFr6 BUF05'.
eapply (srz_sym_ioctl_enotty W E5 o_st6 ms6 _ (Z_to_bv 64 1) ch _ HAI6 HS6 ltac:(img_eqrefl_t) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_eqrefl_t)
ltac:(img_try (eapply fdchan_sbm; [img_try (img_exact Hch) | img_try (img_apply with_vm_backing_same)])) ltac:(img_eqrefl_t) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))).
intros ms6r HS6r Hmm6r.
img_change (resume o_st6 (SLit (2 ^ 64 - 25)) (ss_mem o_st6) (ss_facts o_st6)) with o_af6 in HS6r.
assert (VO6r : VO B ly S W sp0 mem md MUT (ms_mem ms6r) (with_vm_backing (m_vm_lazy md) mat6 md)) by (img_try (rewrite Hmm6r; img_exact VO6)).
assert (BUF06r : aview tfxsegs (w_H W) (ms_mem ms6r) (STDOUT_BUFA) = Some 48) by (img_try (rewrite Hmm6r; img_exact BUF06)).
clear HS6 VO6 BUF06.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E5 o_af6 o_st7 _ _ _ HS6r o_run7) HAI6).
intros W7 c7 _ HAI7 (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). cbn [cfg_model] in HAI7. clear HS6r.
rewrite ?wvb_wvb in HAI7 |- *.
assert (VO7 : VO B ly S W sp0 mem md MUT (ms_mem ms7) (with_vm_backing (m_vm_lazy md) mat7 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms7) mat7 VO6r) as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF7. intros Hin. destruct (vo_windows_sound E5 o_af6 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp5 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- intros x Hx1 Hx2. img_apply HFr7. intros Hin. destruct (vo_windows_sound E5 o_af6 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp5 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- img_apply (vf_band_present_ecall W E5 o_st7 ms7 sp0 HS7 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp5 ltac:(img_lia)). }
assert (BUF07 : aview tfxsegs (w_H W) (ms_mem ms7) (STDOUT_BUFA) = Some 48).
{ rewrite <- BUF06r. img_apply aview_eq_of. img_apply HFr7. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (vo_windows_sound E5 o_af6 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp5 Hin) as [Hw|Hw]; [img_try (unfold vf_band in Hw; GEO) | img_try (unfold vo_file, F_STDOUT, FILE_SZ in Hw; GEO)]. }
clear VO6r HF7 HFr7 BUF06r.
pose proof HS7 as HSc7. destruct HSc7 as (_ & _ & _ & _ & _ & _ & Hregs7 & Hmem7 & HG7). cbn [restrict ms_mem] in Hmem7.
pose proof (lit_buf_sound tfxsegs E5 (mrestrict (w_H W) (ms_mem ms7)) (ss_mem o_st7) (SLit (F_STDOUT + 120)) 4 [1; 0; 0; 0] Hmem7
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as Hfdrd. cbn [sv_denot] in Hfdrd.
pose proof (lit_buf_sound tfxsegs E5 (mrestrict (w_H W) (ms_mem ms7)) (ss_mem o_st7) (SLit (84067 + D_20)) 1 [10] Hmem7
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as Hnlrd.
img_change (map (Z_to_bv 8) [48; 10]) with ([Z_to_bv 8 48] ++ map (Z_to_bv 8) [10]).
eapply (srz_sym_stdio_writev2 W E5 o_st7 ms7 _ (Z_to_bv 64 1) ch 0 2 (-1120) F_STDOUT _ (SLit STDOUT_BUFA) (SLit 1) (SLit (84067 + D_20)) (SLit 1)
([Z_to_bv 8 48]) (map (Z_to_bv 8) [10]) (map (Z_to_bv 8) [1; 0; 0; 0]) 114 T HAI7 HS7 ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t)).
- img_refl.
- eapply fdchan_sbm; [img_try (img_exact Hch) | img_try (img_apply with_vm_backing_same)].
- img_refl.
- img_case; vm_compute. all: img_refl.
- img_refl.
- img_refl.
- img_refl.
- img_refl.
- img_refl.
- match goal with |- U _ ?x = _ => let x' := img_ev constr:(x) in img_change x with x' end. rewrite !U_SLit. img_refl.
- match goal with |- U _ ?x = _ => let x' := img_ev constr:(x) in img_change x with x' end. rewrite U_SLit. img_refl.
- img_refl.
- img_refl.
- cbn. img_lia. - cbn. img_lia. - cbn. img_lia. - cbn. img_lia.
- img_case; vm_compute. all: img_refl.
-   cbn [sv_denot]. img_change (word_to_nat (Z_to_bv 64 1)) with 1%nat.
img_apply (proj2 (rdn_mbytes tfxsegs _ 1%nat STDOUT_BUFA [Z_to_bv 8 48])). split; [img_refl|].
intros i Hi. replace i with 0%nat by img_lia. rewrite Z.add_0_r. destruct (aview_mbyte _ _ _ _ BUF07) as (b & Hb & Hbv).
rewrite Hb. cbn. f_equal. img_apply bv_eq. rewrite Hbv. img_refl.
-   img_change (word_to_nat (sv_denot E5 (SLit 1))) with 1%nat. img_exact Hnlrd.
- rewrite !U_SLit. img_change (zcanon 1) with 1. img_lia.
- rewrite !U_SLit. img_change (zcanon STDOUT_BUFA) with STDOUT_BUFA. img_change (zcanon 1) with 1. unfold STDOUT_BUFA. img_lia.
- rewrite !U_SLit, Usp5. img_change (zcanon STDOUT_BUFA) with STDOUT_BUFA. img_change (zcanon 1) with 1. unfold STDOUT_BUFA. img_lia.
- rewrite !U_SLit. img_change (zcanon (84067 + D_20)) with (84067 + D_20). img_change (zcanon 1) with 1. img_lia.
- rewrite !U_SLit, Usp5. img_change (zcanon (84067 + D_20)) with (84067 + D_20). img_change (zcanon 1) with 1. img_lia.
- img_exact Hfdrd.
- img_case; vm_compute. all: img_refl.
- unfold F_STDOUT. img_lia.
- unfold F_STDOUT. img_lia.
- rewrite Usp5. unfold F_STDOUT. img_lia.
- rewrite Usp5. img_lia.
- rewrite Usp5. img_lia.
- img_case; vm_compute. all: img_refl.
-
intros ms7' ws7 mat7' HS7' HF7' HFr7' HAI7'. rewrite ?wvb_wvb in HAI7' |- *.
img_change (wl_after o_st7 0 (-1120) 114) with o_af7 in HS7'.
remember (havoc E5 114 ws7) as E6 eqn:HE6.
assert (OLD6 : forall j, (j < 114)%nat -> ew E6 j = ew E5 j) by (img_try (intros j Hj; rewrite HE6; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp6 : bv_unsigned (ew E6 2) = sp0) by (img_try (rewrite OLD6 by ((img_case; cbv); img_lia); img_exact Usp5)).
assert (G3_6 : ew E6 3 = w64 (as_gp B)) by (img_try (rewrite OLD6 by ((img_case; cbv); img_lia); img_exact G3_5)).
assert (G4_6 : ew E6 4 = w64 (as_tp B)) by (img_try (rewrite OLD6 by ((img_case; cbv); img_lia); img_exact G4_5)).
assert (G12_6 : bv_unsigned (ew E6 12) = ap) by (img_try (rewrite OLD6 by ((img_case; cbv); img_lia); img_exact G12_5)).
assert (HAE6 : env_agree 32 EA E6)
by (img_try (rewrite HE6; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (img_exact HAE5)])).
assert (VO7' : VO B ly S W sp0 mem md MUT (ms_mem ms7') (with_vm_backing (m_vm_lazy md) mat7' md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms7') mat7' VO7) as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF7'. intros Hin. destruct (vo_windows_sound E5 o_st7 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp5 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- intros x Hx1 Hx2. img_apply HFr7'. intros Hin. destruct (vo_windows_sound E5 o_st7 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp5 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- img_apply (vf_band_present W E6 o_af7 ms7' sp0 HS7' ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 ltac:(img_lia)). }
clear HE6 HS7 VO7 Hfdrd Hnlrd Hregs7 Hmem7 HG7 HF7' HFr7' BUF07.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E6 o_af7 o_st8 _ _ _ HS7' o_run8) HAI7').
intros W8 c8 _ HAI8 (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). cbn [cfg_model] in HAI8. clear HS7'.
rewrite ?wvb_wvb in HAI8 |- *.
assert (VO8 : VO B ly S W sp0 mem md MUT (ms_mem ms8) (with_vm_backing (m_vm_lazy md) mat8 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms8) mat8 VO7') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF8. intros Hin. destruct (vo_windows_sound E6 o_af7 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- intros x Hx1 Hx2. img_apply HFr8. intros Hin. destruct (vo_windows_sound E6 o_af7 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- img_apply (vf_band_present W E6 o_st8 ms8 sp0 HS8 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 ltac:(img_lia)). }
clear VO7' HF8 HFr8.
assert (SRA8' : range_addressable (aview tfxsegs (w_H W) (ms_mem ms8)) SHADOW_OFF (84068 + D_20) 0) by (img_try (intros y Hy; img_lia)).
assert (SHU8' : 0 < 0 -> shadow_hull_vis (aview tfxsegs (w_H W) (ms_mem ms8)) (84068 + D_20) 0) by (img_try (intros H0; img_lia)).
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_memcpy_ext B LAWS AMEMCPY W E6 o_st8 ms8 _ ly S sp0 o_r08 o_rest8 125 RA_FX OSP_FX
(SLit STDOUT_BUFA) (SLit (84068 + D_20)) (SLit 0) (STDOUT_BUFA) ((84068 + D_20)) 0
HS8 ltac:(img_try (rewrite HBcode; img_refl)) ltac:(img_eqrefl_t) Usp6 G3_6 G4_6 ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t)
ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t)
ltac:(img_eqrefl_t) ltac:(img_refl) ltac:(img_eqrefl_t) ltac:(img_refl) ltac:(img_eqrefl_t) ltac:(img_refl)
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_lia)
ltac:(img_try (unfold RA_FX; img_lia)) ltac:(img_refl)
ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_try (GEO))
ltac:(img_try (left; unfold kLowMemEnd; GEO))
ltac:(img_try (first [left; unfold kLowMemEnd; GEO | eapply (vf_stack_amem B); [img_try (img_exact (proj1 VO8)) | img_try (img_exact Hstk) | img_try (img_exact HtopS) | img_try (GEO) | img_try (GEO)]]))
(vo_rest_disj E6 sp0 ap o_rest8 (STDOUT_BUFA) 0 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_6 Hap1 Hsp44 ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_lia))
(vo_rest_ok E6 sp0 ap o_rest8 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_6 Hap1 Hap2)
(vo_rest_w E6 o_rest8 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VO8) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VO8)))
ltac:(img_try (intros a Ha; img_lia)) SRA8' SHU8'
ltac:(img_try (intros a Ha; img_lia)) ltac:(img_try (intros y Hy; img_lia)) ltac:(img_try (intros H0; img_lia))) HAI8).
intros W8' c8' _ HAI8' (-> & ms8' & mat8' & -> & HS8' & HAR8' & HP8' & Heff8' & Hfr8' & Hpm8'). cbn [cfg_model] in HAI8'.
rewrite wvb_wvb in HAI8', HAR8' |- *.
img_change (vf_after_icpt 125 o_st8 RA_FX OSP_FX 0 []) with o_af8 in HS8'.
assert (VO8' : VO B ly S W sp0 mem md MUT (ms_mem ms8') (with_vm_backing (m_vm_lazy md) mat8' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms8) _ (ms_mem ms8') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ ((STDOUT_BUFA) <= a < (STDOUT_BUFA) + 0))).
- img_exact VO8.
- img_exact HAR8'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat8' mat8 md). img_apply with_vm_backing_same.
- intros a [Ha|Ha]; [img_try (left; unfold vf_band, OSP_FX in *; img_lia) | img_try (right; unfold MUT, vo_mut; GEO)].
- intros a Hr Hna. img_apply Hfr8'; [img_try (img_exact Hr) | img_try (intros H'; img_apply Hna; left; img_exact H') | img_try (intros H'; img_apply Hna; right; img_exact H')].
- img_exact Hpm8'. }
remember (havoc E6 125 (map (getr (ms_regs ms8')) CLOB)) as E7 eqn:HE7.
assert (OLD7 : forall j, (j < 125)%nat -> ew E7 j = ew E6 j) by (img_try (intros j Hj; rewrite HE7; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp7 : bv_unsigned (ew E7 2) = sp0) by (img_try (rewrite OLD7 by ((img_case; cbv); img_lia); img_exact Usp6)).
assert (G3_7 : ew E7 3 = w64 (as_gp B)) by (img_try (rewrite OLD7 by ((img_case; cbv); img_lia); img_exact G3_6)).
assert (G4_7 : ew E7 4 = w64 (as_tp B)) by (img_try (rewrite OLD7 by ((img_case; cbv); img_lia); img_exact G4_6)).
assert (G12_7 : bv_unsigned (ew E7 12) = ap) by (img_try (rewrite OLD7 by ((img_case; cbv); img_lia); img_exact G12_6)).
assert (HAE7 : env_agree 32 EA E7)
by (img_try (rewrite HE7; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (img_exact HAE6)])).
clear HE7 HS8 VO8 SRA8' SHU8' Heff8'.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E7 o_af8 o_st9 _ _ _ HS8' o_run9) HAI8').
intros W9 c9 _ HAI9 (-> & ms9 & mat9 & -> & HS9 & HF9 & HFr9). cbn [cfg_model] in HAI9. clear HS8'.
rewrite ?wvb_wvb in HAI9 |- *.
assert (VO9 : VO B ly S W sp0 mem md MUT (ms_mem ms9) (with_vm_backing (m_vm_lazy md) mat9 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms9) mat9 VO8') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF9. intros Hin. destruct (vo_windows_sound E7 o_af8 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp7 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- intros x Hx1 Hx2. img_apply HFr9. intros Hin. destruct (vo_windows_sound E7 o_af8 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp7 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- img_apply (vf_band_present W E7 o_st9 ms9 sp0 HS9 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp7 ltac:(img_lia)). }
clear VO8' HF9 HFr9.
eapply (SRr_srealizes tfxsegs W _
(fun W' c' => W' = W /\ exists mat', c' = mkCfg (mkst (ms_regs ms9) (v_jalr (getr (ms_regs ms9) 1) 0) (ms_mem ms9) (seg_rom tfxsegs))
(with_vm_backing (m_vm_lazy md) mat' md)) T); [ | img_try (img_exact HAI9) | ].
{ eapply (SRr_ret_at tfxsegs tfxmusl_tbl tfxmusl_tbl_ok Hwx W E7); [img_try (img_exact HS9) | img_refl | img_try ((try img_inst; img_case; vm_compute); img_refl) |].
intros mat'. rewrite wvb_wvb. split; [img_refl|]. exists mat'. img_refl. }
intros WR cR _ HAIR (-> & matR & ->). cbn [cfg_model] in HAIR.
destruct VO9 as (HAR9 & Hsbm9 & Hpb9 & Hfr9 & Hpm9).
rreg HS9 (1%bv : bv 5) Q1.
rewrite OLD7, OLD6, OLD5, OLD4, OLD3, OLD2, OLD1 in Q1 by (img_try ((img_case; cbv); img_lia)). rewrite E0_1 in Q1.
pose proof (st_ok_restrict_reg tfxsegs (w_H W) E7 _ _ 10 HS9) as Q10. cbn [ms_regs restrict] in Q10.
match type of Q10 with _ = sv_denot _ ?v => let v' := img_ev constr:(v) in img_change v with v' in Q10 end. cbn [sv_denot] in Q10.
replace (v_jalr (getr (ms_regs ms9) 1) 0) with (w64 (raZ regs))
by (img_try (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; img_exact Hra)).
assert (SBMR : same_but_materialized (with_vm_backing (m_vm_lazy md) mat9 md) (with_vm_backing (m_vm_lazy md) matR md))
by (img_try (rewrite <- (wvb_collapse (m_vm_lazy md) matR mat9 md); img_apply with_vm_backing_same)).
pose proof (same_but_materialized_frame _ _ SBMR) as MF.
img_apply (HK (ms_regs ms9) (ms_mem ms9) (with_vm_backing (m_vm_lazy md) matR md)).
* img_apply (al_frame _ _ LAWS ly S W (ms_mem ms9) _ (ms_mem ms9) _ HAR9); [img_try (intros; img_refl) | img_try (intros a Hv; img_exact Hv) | img_try (img_apply MF) | img_try (img_apply MF) | img_try (img_apply MF) | img_try (img_exact (YE0v.hs_kept_refl _ _))].
* img_exact (aregs_preserved_of_st_ok _ E7 _ _ regs _ HS9 HAE7 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))).
* img_apply with_vm_backing_same.
* rewrite Q10. img_refl.
* destruct HS9 as (_ & _ & _ & _ & _ & _ & _ & Hmem9 & _).
split.
-- unfold ofile_is, stdout_fields1.
repeat img_apply Forall_cons; try img_apply Forall_nil;
(eapply (val_mem_of_lit E7 (mrestrict (w_H W) (ms_mem ms9)) (ss_mem o_st9) _ _ _ Hmem9); (try img_inst; img_case; vm_compute); img_refl).
-- eapply (val_mem_of_lit E7 (mrestrict (w_H W) (ms_mem ms9)) (ss_mem o_st9) _ _ _ Hmem9); (try img_inst; img_case; vm_compute); img_refl.
* img_exact Hfr9.
* img_exact Hpm9.
* img_exact HAIR.
Qed.
Theorem tfx_vfprintf_stdout_next : forall ly S (W : world tfxsegs) regs mem md ap cval wp T,
ecall_pre tfxsegs B ly S W regs mem md ->
2 ^ 44 <= spZ regs -> ly_stk_lo ly + VF_STK <= spZ regs ->
(forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) ->
getr regs 10 = w64 F_STDOUT -> getr regs 11 = w64 FMT_d -> getr regs 12 = w64 ap ->
spZ regs <= ap -> ap + 8 <= 2 ^ 47 -> ap mod 8 = 0 ->
val_mem tfxsegs (mrestrict (w_H W) mem) ap 8 0 ->
stdout_mid wp (mrestrict (w_H W) mem) -> STDOUT_BUFA <= wp -> wp + 2 <= STDOUT_BUFA + STDOUT_BSZ ->
(forall a, vo_file a \/ STDOUT_BUFA <= a < STDOUT_BUFA + STDOUT_BSZ -> ~ aowned B ly S a) ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
ro_img (mrestrict (w_H W) mem) ->
range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF STDOUT_BUFA STDOUT_BSZ ->
shadow_hull_vis (aview tfxsegs (w_H W) mem) STDOUT_BUFA STDOUT_BSZ ->
range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF FMT_d 4 ->
shadow_hull_vis (aview tfxsegs (w_H W) mem) FMT_d 4 ->
AI tfxsegs (w_H W) (w_A W) md ->
(forall regs' mem' md',
AR tfxsegs B ly S W mem' md' -> aregs_preserved regs regs' -> same_but_materialized md md' ->
getr regs' 10 = w64 2 ->
stdout_mid (wp + 2) (mrestrict (w_H W) mem') ->
aview tfxsegs (w_H W) mem' wp = Some 48 -> aview tfxsegs (w_H W) mem' (wp + 1) = Some 10 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_band (spZ regs) a -> ~ vo_mut wp (wp + 2) a ->
aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vo_mut wp (wp + 2) a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
AI tfxsegs (w_H W) (w_A W) md' ->
srealizes tfxsegs (cfg_at tfxsegs (raZ regs) regs' mem' md') T) ->
srealizes tfxsegs (cfg_at tfxsegs A_vfprintf regs mem md) T.
Proof.
intros ly S W regs mem md ap cval wp T HPRE Hsp44 Hstk Hpres Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg
HFP Hwp1 Hwp2 HBown Hgot Hcan Hcv Hro Hra_b Hhull_b Hra_f Hhull_f HAI0 HK.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by img_refl. assert (HVF : VF_STK = 9104) by img_refl.
assert (HFF : F_STDOUT = (682048 + D_10f0)) by img_refl. assert (HFS : FILE_SZ = 232) by img_refl.
assert (HBF : STDOUT_BUFA = (6281312 + D_10c0)) by img_refl. assert (HBS : STDOUT_BSZ = 1024) by img_refl.
assert (HFD : FMT_d = (84065 + D_20)) by img_refl. assert (HPO : PAD_OFF = -736) by img_refl. assert (HOX : OSP_FX = -976) by img_refl.
assert (HBE : BUFEND = (6282336 + D_10c0)) by img_refl.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by img_refl.
set (sp0 := spZ regs) in *. assert (HtopS : sp0 < kHighMemEnd) by (img_try (rewrite KHI; img_lia)).
assert (Hsp47 : sp0 <= 2 ^ 47) by img_lia.
set (MUT := vo_mut wp (wp + 2)) in *.
assert (MUTimg : forall a, MUT a -> img_byte_ok tfxsegs a = true) by (img_try (intros a Ha; img_apply (vo_mut_img wp (wp + 2) a); [img_lia | img_lia | img_try (img_exact Ha)])).
assert (MUTdec : forall a, MUT a \/ ~ MUT a) by (img_try (intros a; img_apply vo_mut_dec)).
assert (HFownM : forall a, MUT a -> ~ aowned B ly S a) by (img_try (intros a [Ha|Ha]; img_apply HBown; [img_try (left; img_exact Ha) | img_try (right; img_lia)])).
unfold cfg_at. img_change (w64 A_vfprintf) with (Z_to_bv 64 A_vfprintf).
pose proof (vo_entry1 W regs mem ap cval wp Hsp44 Hsp47 Hal16 ltac:(img_try (intros a Ha; img_apply Hpres; img_exact Ha)) Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg
HFP ltac:(img_lia) Hgot Hcan Hcv Hro) as HS0.
set (EL := [Z_to_bv 64 0; Z_to_bv 64 cval; Z_to_bv 64 wp]) in *.
remember (Ereg regs EL) as E0 eqn:HE0.
assert (EE : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E0 i = getr regs r)
by (img_try (intros i r Hi; rewrite HE0; img_exact (ew_Ereg_nat regs _ i r Hi))).
pose proof (EE 1%nat (1%bv : bv 5) ltac:(img_eqrefl_t)) as E0_1.
assert (Usp0 : bv_unsigned (ew E0 2) = sp0) by (img_try (rewrite (EE 2%nat (2%bv : bv 5) ltac:(img_eqrefl_t)); img_refl)).
assert (G3_0 : ew E0 3 = w64 (as_gp B)) by (img_try (rewrite (EE 3%nat (3%bv : bv 5) ltac:(img_eqrefl_t)); img_exact Hgp)).
assert (G4_0 : ew E0 4 = w64 (as_tp B)) by (img_try (rewrite (EE 4%nat (4%bv : bv 5) ltac:(img_eqrefl_t)); img_exact Htp)).
assert (G12_0 : bv_unsigned (ew E0 12) = ap) by (img_try (rewrite (EE 12%nat (12%bv : bv 5) ltac:(img_eqrefl_t)), Ha2; img_apply unsigned_lit_small; img_lia)).
assert (A34_0 : bv_unsigned (ew E0 34) = wp) by (img_try (rewrite HE0; pose proof (ew_Ereg_extra regs EL 2) as X; cbn [nth Nat.add EL] in X; rewrite X; img_apply unsigned_lit_small; img_lia)).
assert (HAE0 : env_agree 32 (Ereg regs EL) E0) by (img_try (rewrite HE0; split; [img_try (intros i Hi; img_refl) | img_refl])).
set (EA := Ereg regs EL) in *.
clear HE0 EE.
pose proof (VO_init B ly S W sp0 mem md MUT HAR Hpres) as VO0.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E0 ss_vo1 n_st1 _ _ _ HS0 n_run1) HAI0).
intros W1 c1 _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [cfg_model] in HAI1. clear HS0.
rewrite ?wvb_wvb in HAI1 |- *.
assert (VO1 : VO B ly S W sp0 mem md MUT (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms1) mat1 VO0) as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF1. intros Hin. destruct (vo_windows_sound E0 ss_vo1 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- intros x Hx1 Hx2. img_apply HFr1. intros Hin. destruct (vo_windows_sound E0 ss_vo1 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- img_apply (vf_band_present W E0 n_st1 ms1 sp0 HS1 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 ltac:(img_lia)). }
clear VO0 HF1 HFr1.
pose proof (st_ok_add_cond tfxsegs E0 n_st1 _ BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (0 - BUFEND))) (SLit 0) HS1 ltac:(img_try (rewrite branch_geu_U, U_SLit; img_change (zcanon 0) with 0; img_apply Bool.negb_true_iff; img_apply Z.ltb_ge; pose proof (U_range E0 (SAlu ALU_SUB (SLit 0) (SOff 34 (0 - BUFEND)))); img_lia))) as HS1c.
img_change (YQ09.add_cond n_st1 (mkAC BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (0 - BUFEND))) (SLit 0))) with n_st1c in HS1c. clear HS1.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E0 n_st1c n_st2 _ _ _ HS1c n_run2) HAI1).
intros W2 c2 _ HAI2 (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). cbn [cfg_model] in HAI2. clear HS1c.
rewrite ?wvb_wvb in HAI2 |- *.
assert (VO2 : VO B ly S W sp0 mem md MUT (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms2) mat2 VO1) as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF2. intros Hin. destruct (vo_windows_sound E0 n_st1c sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- intros x Hx1 Hx2. img_apply HFr2. intros Hin. destruct (vo_windows_sound E0 n_st1c sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- img_apply (vf_band_present W E0 n_st2 ms2 sp0 HS2 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 ltac:(img_lia)). }
clear VO1 HF2 HFr2.
assert (SRA2' : range_addressable (aview tfxsegs (w_H W) (ms_mem ms2)) SHADOW_OFF (FMT_d) 0) by (img_try (intros y Hy; img_lia)).
assert (SHU2' : 0 < 0 -> shadow_hull_vis (aview tfxsegs (w_H W) (ms_mem ms2)) (FMT_d) 0) by (img_try (intros H0; img_lia)).
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_memcpy_ext B LAWS AMEMCPY W E0 n_st2 ms2 _ ly S sp0 n_r02 n_rest2 35 RA_FX OSP_FX
(SOff 34 0) (SLit FMT_d) (SLit 0) (wp) (FMT_d) 0
HS2 ltac:(img_try (rewrite HBcode; img_refl)) ltac:(img_eqrefl_t) Usp0 G3_0 G4_0 ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t)
ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t)
ltac:(img_eqrefl_t) ltac:(img_try (cbn [sv_denot]; rewrite Z.add_0_r, A34_0; img_refl)) ltac:(img_eqrefl_t) ltac:(img_refl) ltac:(img_eqrefl_t) ltac:(img_refl)
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_lia)
ltac:(img_try (unfold RA_FX; img_lia)) ltac:(img_refl)
ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_try (GEO))
ltac:(img_try (left; unfold kLowMemEnd; GEO))
ltac:(img_try (first [left; unfold kLowMemEnd; GEO | eapply (vf_stack_amem B); [img_try (img_exact (proj1 VO2)) | img_try (img_exact Hstk) | img_try (img_exact HtopS) | img_try (GEO) | img_try (GEO)]]))
(vo_rest_disj E0 sp0 ap n_rest2 (wp) 0 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_0 Hap1 Hsp44 ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_lia))
(vo_rest_ok E0 sp0 ap n_rest2 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_0 Hap1 Hap2)
(vo_rest_w E0 n_rest2 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VO2) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VO2)))
ltac:(img_try (intros a Ha; img_lia)) SRA2' SHU2'
ltac:(img_try (intros a Ha; img_lia)) ltac:(img_try (intros y Hy; img_lia)) ltac:(img_try (intros H0; img_lia))) HAI2).
intros W2' c2' _ HAI2' (-> & ms2' & mat2' & -> & HS2' & HAR2' & HP2' & Heff2' & Hfr2' & Hpm2'). cbn [cfg_model] in HAI2'.
rewrite wvb_wvb in HAI2', HAR2' |- *.
img_change (vf_after_icpt 35 n_st2 RA_FX OSP_FX 0 []) with n_af2 in HS2'.
assert (VO2' : VO B ly S W sp0 mem md MUT (ms_mem ms2') (with_vm_backing (m_vm_lazy md) mat2' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms2) _ (ms_mem ms2') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ ((wp) <= a < (wp) + 0))).
- img_exact VO2.
- img_exact HAR2'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat2' mat2 md). img_apply with_vm_backing_same.
- intros a [Ha|Ha]; [img_try (left; unfold vf_band, OSP_FX in *; img_lia) | img_try (right; unfold MUT, vo_mut; GEO)].
- intros a Hr Hna. img_apply Hfr2'; [img_try (img_exact Hr) | img_try (intros H'; img_apply Hna; left; img_exact H') | img_try (intros H'; img_apply Hna; right; img_exact H')].
- img_exact Hpm2'. }
remember (havoc E0 35 (map (getr (ms_regs ms2')) CLOB)) as E1 eqn:HE1.
assert (OLD1 : forall j, (j < 35)%nat -> ew E1 j = ew E0 j) by (img_try (intros j Hj; rewrite HE1; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp1 : bv_unsigned (ew E1 2) = sp0) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact Usp0)).
assert (G3_1 : ew E1 3 = w64 (as_gp B)) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact G3_0)).
assert (G4_1 : ew E1 4 = w64 (as_tp B)) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact G4_0)).
assert (G12_1 : bv_unsigned (ew E1 12) = ap) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact G12_0)).
assert (A34_1 : bv_unsigned (ew E1 34) = wp) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact A34_0)).
assert (HAE1 : env_agree 32 EA E1)
by (img_try (rewrite HE1; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (img_exact HAE0)])).
clear HE1 HS2 VO2 SRA2' SHU2' Heff2'.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E1 n_af2 n_st3 _ _ _ HS2' n_run3) HAI2').
intros W3 c3 _ HAI3 (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). cbn [cfg_model] in HAI3. clear HS2'.
rewrite ?wvb_wvb in HAI3 |- *.
assert (VO3 : VO B ly S W sp0 mem md MUT (ms_mem ms3) (with_vm_backing (m_vm_lazy md) mat3 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms3) mat3 VO2') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF3. intros Hin. destruct (vo_windows_sound E1 n_af2 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp1 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- intros x Hx1 Hx2. img_apply HFr3. intros Hin. destruct (vo_windows_sound E1 n_af2 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp1 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- img_apply (vf_band_present W E1 n_st3 ms3 sp0 HS3 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp1 ltac:(img_lia)). }
clear VO2' HF3 HFr3.
assert (SRA3' : range_addressable (aview tfxsegs (w_H W) (ms_mem ms3)) SHADOW_OFF ((68452 + D_20)) 0) by (img_try (intros y Hy; img_lia)).
assert (SHU3' : 0 < 0 -> shadow_hull_vis (aview tfxsegs (w_H W) (ms_mem ms3)) ((68452 + D_20)) 0) by (img_try (intros H0; img_lia)).
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_memcpy_ext B LAWS AMEMCPY W E1 n_st3 ms3 _ ly S sp0 n_r03 n_rest3 51 RA_FX OSP_FX
(SOff 34 0) (SLit (68452 + D_20)) (SLit 0) (wp) ((68452 + D_20)) 0
HS3 ltac:(img_try (rewrite HBcode; img_refl)) ltac:(img_eqrefl_t) Usp1 G3_1 G4_1 ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t)
ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t)
ltac:(img_eqrefl_t) ltac:(img_try (cbn [sv_denot]; rewrite Z.add_0_r, A34_1; img_refl)) ltac:(img_eqrefl_t) ltac:(img_refl) ltac:(img_eqrefl_t) ltac:(img_refl)
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_lia)
ltac:(img_try (unfold RA_FX; img_lia)) ltac:(img_refl)
ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_try (GEO))
ltac:(img_try (left; unfold kLowMemEnd; GEO))
ltac:(img_try (first [left; unfold kLowMemEnd; GEO | eapply (vf_stack_amem B); [img_try (img_exact (proj1 VO3)) | img_try (img_exact Hstk) | img_try (img_exact HtopS) | img_try (GEO) | img_try (GEO)]]))
(vo_rest_disj E1 sp0 ap n_rest3 (wp) 0 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_1 Hap1 Hsp44 ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_lia))
(vo_rest_ok E1 sp0 ap n_rest3 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_1 Hap1 Hap2)
(vo_rest_w E1 n_rest3 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VO3) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VO3)))
ltac:(img_try (intros a Ha; img_lia)) SRA3' SHU3'
ltac:(img_try (intros a Ha; img_lia)) ltac:(img_try (intros y Hy; img_lia)) ltac:(img_try (intros H0; img_lia))) HAI3).
intros W3' c3' _ HAI3' (-> & ms3' & mat3' & -> & HS3' & HAR3' & HP3' & Heff3' & Hfr3' & Hpm3'). cbn [cfg_model] in HAI3'.
rewrite wvb_wvb in HAI3', HAR3' |- *.
img_change (vf_after_icpt 51 n_st3 RA_FX OSP_FX 0 []) with n_af3 in HS3'.
assert (VO3' : VO B ly S W sp0 mem md MUT (ms_mem ms3') (with_vm_backing (m_vm_lazy md) mat3' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms3) _ (ms_mem ms3') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ ((wp) <= a < (wp) + 0))).
- img_exact VO3.
- img_exact HAR3'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat3' mat3 md). img_apply with_vm_backing_same.
- intros a [Ha|Ha]; [img_try (left; unfold vf_band, OSP_FX in *; img_lia) | img_try (right; unfold MUT, vo_mut; GEO)].
- intros a Hr Hna. img_apply Hfr3'; [img_try (img_exact Hr) | img_try (intros H'; img_apply Hna; left; img_exact H') | img_try (intros H'; img_apply Hna; right; img_exact H')].
- img_exact Hpm3'. }
remember (havoc E1 51 (map (getr (ms_regs ms3')) CLOB)) as E2 eqn:HE2.
assert (OLD2 : forall j, (j < 51)%nat -> ew E2 j = ew E1 j) by (img_try (intros j Hj; rewrite HE2; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp2 : bv_unsigned (ew E2 2) = sp0) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact Usp1)).
assert (G3_2 : ew E2 3 = w64 (as_gp B)) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact G3_1)).
assert (G4_2 : ew E2 4 = w64 (as_tp B)) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact G4_1)).
assert (G12_2 : bv_unsigned (ew E2 12) = ap) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact G12_1)).
assert (A34_2 : bv_unsigned (ew E2 34) = wp) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact A34_1)).
assert (HAE2 : env_agree 32 EA E2)
by (img_try (rewrite HE2; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (img_exact HAE1)])).
clear HE2 HS3 VO3 SRA3' SHU3' Heff3'.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E2 n_af3 n_st4 _ _ _ HS3' n_run4) HAI3').
intros W4 c4 _ HAI4 (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). cbn [cfg_model] in HAI4. clear HS3'.
rewrite ?wvb_wvb in HAI4 |- *.
assert (VO4 : VO B ly S W sp0 mem md MUT (ms_mem ms4) (with_vm_backing (m_vm_lazy md) mat4 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms4) mat4 VO3') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF4. intros Hin. destruct (vo_windows_sound E2 n_af3 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp2 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- intros x Hx1 Hx2. img_apply HFr4. intros Hin. destruct (vo_windows_sound E2 n_af3 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp2 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- img_apply (vf_band_present W E2 n_st4 ms4 sp0 HS4 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp2 ltac:(img_lia)). }
clear VO3' HF4 HFr4.
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_memset B LAWS AMEMSET W E2 n_st4 ms4 _ ly S sp0 n_r04 n_rest4 67 RA_PAD OSP_PC PAD_OFF 48 1%nat
HS4 ltac:(img_try (rewrite HBcode; img_refl)) ltac:(img_eqrefl_t) Usp2 G3_2 G4_2 ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t)
ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_lia) ltac:(img_refl)
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_PC; img_lia)) ltac:(img_try (unfold OSP_PC, PAD_OFF; img_lia)) ltac:(img_try (unfold PAD_OFF; cbn; img_lia)) ltac:(img_try (unfold RA_PAD; img_lia)) ltac:(img_refl)
(vo_rest_ok E2 sp0 ap n_rest4 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_2 Hap1 Hap2)
(vo_rest_w E2 n_rest4 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VO4) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VO4)))) HAI4).
intros W4' c4' _ HAI4' (-> & ms4' & mat4' & -> & HS4' & HAR4' & HP4' & Hfr4' & Hpm4'). cbn [cfg_model] in HAI4'.
rewrite wvb_wvb in HAI4', HAR4' |- *.
img_change (vf_after_icpt 67 n_st4 RA_PAD OSP_PC PAD_OFF (repeat 48 1%nat)) with n_af4 in HS4'.
assert (VO4' : VO B ly S W sp0 mem md MUT (ms_mem ms4') (with_vm_backing (m_vm_lazy md) mat4' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms4) _ (ms_mem ms4') _
(fun a => (sp0 + OSP_PC - ESTACK <= a < sp0 + OSP_PC) \/ (sp0 + PAD_OFF <= a < sp0 + PAD_OFF + 1))).
- img_exact VO4.
- img_exact HAR4'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat4' mat4 md). img_apply with_vm_backing_same.
- intros a Ha. left. unfold vf_band, OSP_PC, PAD_OFF in *. img_lia.
- intros a Hr Hna. img_apply Hfr4'; [img_try (img_exact Hr) | img_try (intros H'; img_apply Hna; left; img_exact H') | img_try (intros H'; img_apply Hna; right; cbn; img_exact H')].
- img_exact Hpm4'. }
remember (havoc E2 67 (map (getr (ms_regs ms4')) CLOB)) as E3 eqn:HE3.
assert (OLD3 : forall j, (j < 67)%nat -> ew E3 j = ew E2 j) by (img_try (intros j Hj; rewrite HE3; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp3 : bv_unsigned (ew E3 2) = sp0) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact Usp2)).
assert (G3_3 : ew E3 3 = w64 (as_gp B)) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact G3_2)).
assert (G4_3 : ew E3 4 = w64 (as_tp B)) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact G4_2)).
assert (G12_3 : bv_unsigned (ew E3 12) = ap) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact G12_2)).
assert (A34_3 : bv_unsigned (ew E3 34) = wp) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact A34_2)).
assert (HAE3 : env_agree 32 EA E3)
by (img_try (rewrite HE3; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (img_exact HAE2)])).
clear HE3 HS4 VO4.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E3 n_af4 n_st5 _ _ _ HS4' n_run5) HAI4').
intros W5 c5 _ HAI5 (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). cbn [cfg_model] in HAI5. clear HS4'.
rewrite ?wvb_wvb in HAI5 |- *.
assert (VO5 : VO B ly S W sp0 mem md MUT (ms_mem ms5) (with_vm_backing (m_vm_lazy md) mat5 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms5) mat5 VO4') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF5. intros Hin. destruct (vo_windows_sound E3 n_af4 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp3 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- intros x Hx1 Hx2. img_apply HFr5. intros Hin. destruct (vo_windows_sound E3 n_af4 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp3 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- img_apply (vf_band_present W E3 n_st5 ms5 sp0 HS5 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp3 ltac:(img_lia)). }
clear VO4' HF5 HFr5.
pose proof (st_ok_add_cond tfxsegs E3 n_st5 _ BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (0 - BUFEND))) (SLit 1) HS5 ltac:(img_try (rewrite branch_geu_U, U_neg_off, U_SLit by (rewrite A34_3; unfold M64; img_lia); rewrite A34_3; img_change (zcanon 1) with 1; img_apply Bool.negb_true_iff; img_apply Z.ltb_ge; img_lia))) as HS5c.
img_change (YQ09.add_cond n_st5 (mkAC BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (0 - BUFEND))) (SLit 1))) with n_st5c in HS5c. clear HS5.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E3 n_st5c n_st6 _ _ _ HS5c n_run6) HAI5).
intros W6 c6 _ HAI6 (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). cbn [cfg_model] in HAI6. clear HS5c.
rewrite ?wvb_wvb in HAI6 |- *.
assert (VO6 : VO B ly S W sp0 mem md MUT (ms_mem ms6) (with_vm_backing (m_vm_lazy md) mat6 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms6) mat6 VO5) as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF6. intros Hin. destruct (vo_windows_sound E3 n_st5c sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp3 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- intros x Hx1 Hx2. img_apply HFr6. intros Hin. destruct (vo_windows_sound E3 n_st5c sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp3 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- img_apply (vf_band_present W E3 n_st6 ms6 sp0 HS6 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp3 ltac:(img_lia)). }
clear VO5 HF6 HFr6.
pose proof HS6 as HSc6. destruct HSc6 as (_ & _ & _ & _ & _ & _ & _ & Hmem6 & _). cbn [restrict ms_mem] in Hmem6.
assert (PAD6 : aview tfxsegs (w_H W) (ms_mem ms6) (sp0 + PAD_OFF) = Some 48).
{ replace (sp0 + PAD_OFF) with (sp0 + PAD_OFF + Z.of_nat 0) by img_lia.
img_apply (lit_buf_aview W E3 (ms_mem ms6) (ss_mem n_st6) (SOff 2 PAD_OFF) (sp0 + PAD_OFF) 1 [48] Hmem6 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try (cbn [sv_denot]; rewrite Usp3; img_refl)) ltac:(img_try (repeat constructor; img_lia)) 0%nat ltac:(img_lia)). }
clear Hmem6.
destruct (vf_stack_shadow B LAWS W ly S (ms_mem ms6) _ sp0 (sp0 + PAD_OFF) 1 (proj1 VO6) Hstk Htop ltac:(img_try (unfold PAD_OFF; img_lia)) ltac:(img_try (unfold PAD_OFF; img_lia)) ltac:(img_lia)) as [SRA6' SHU6'].
destruct (vo_shadow_xfer B ly S W sp0 mem md wp (wp + 2) (ms_mem ms6) _ STDOUT_BUFA STDOUT_BSZ wp 1 VO6 ltac:(img_lia) Hstk Hra_b Hhull_b
ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) ltac:(img_try (rewrite KHI; img_lia))) as [DRA6' DHU6'].
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_memcpy_ext B LAWS AMEMCPY W E3 n_st6 ms6 _ ly S sp0 n_r06 n_rest6 83 RA_FX OSP_FX
(SOff 34 0) (SOff 2 PAD_OFF) (SLit 1) (wp) (sp0 + PAD_OFF) 1
HS6 ltac:(img_try (rewrite HBcode; img_refl)) ltac:(img_eqrefl_t) Usp3 G3_3 G4_3 ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t)
ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t)
ltac:(img_eqrefl_t) ltac:(img_try (cbn [sv_denot]; rewrite Z.add_0_r, A34_3; img_refl)) ltac:(img_eqrefl_t) ltac:(img_try (cbn [sv_denot]; rewrite Usp3; img_refl)) ltac:(img_eqrefl_t) ltac:(img_refl)
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_lia)
ltac:(img_try (unfold RA_FX; img_lia)) ltac:(img_refl)
ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_try (GEO))
ltac:(img_try (left; unfold kLowMemEnd; GEO))
ltac:(img_try (first [left; unfold kLowMemEnd; GEO | eapply (vf_stack_amem B); [img_try (img_exact (proj1 VO6)) | img_try (img_exact Hstk) | img_try (img_exact HtopS) | img_try (GEO) | img_try (GEO)]]))
(vo_rest_disj E3 sp0 ap n_rest6 (wp) 1 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_3 Hap1 Hsp44 ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_lia))
(vo_rest_ok E3 sp0 ap n_rest6 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_3 Hap1 Hap2)
(vo_rest_w E3 n_rest6 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VO6) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VO6)))
ltac:(img_try (intros a Ha; replace a with (sp0 + PAD_OFF) by img_lia; rewrite PAD6; discriminate)) SRA6' SHU6'
ltac:(img_try (intros a Ha; split; [img_try (img_apply stdout_buf_writable; img_lia) | img_try (img_apply HBown; right; img_lia)])) ltac:(img_try (img_exact DRA6')) ltac:(img_try (img_exact DHU6'))) HAI6).
intros W6' c6' _ HAI6' (-> & ms6' & mat6' & -> & HS6' & HAR6' & HP6' & Heff6' & Hfr6' & Hpm6'). cbn [cfg_model] in HAI6'.
rewrite wvb_wvb in HAI6', HAR6' |- *.
img_change (vf_after_icpt 83 n_st6 RA_FX OSP_FX 0 []) with n_af6 in HS6'.
assert (VO6' : VO B ly S W sp0 mem md MUT (ms_mem ms6') (with_vm_backing (m_vm_lazy md) mat6' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms6) _ (ms_mem ms6') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ ((wp) <= a < (wp) + 1))).
- img_exact VO6.
- img_exact HAR6'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat6' mat6 md). img_apply with_vm_backing_same.
- intros a [Ha|Ha]; [img_try (left; unfold vf_band, OSP_FX in *; img_lia) | img_try (right; unfold MUT, vo_mut; GEO)].
- intros a Hr Hna. img_apply Hfr6'; [img_try (img_exact Hr) | img_try (intros H'; img_apply Hna; left; img_exact H') | img_try (intros H'; img_apply Hna; right; img_exact H')].
- img_exact Hpm6'. }
assert (BUFA6' : aview tfxsegs (w_H W) (ms_mem ms6') (wp) = Some 48).
{ rewrite <- PAD6, <- (Z.add_0_r wp), <- (Z.add_0_r (sp0 + PAD_OFF)). img_apply (Heff6' 0). img_lia. }
remember (havoc E3 83 (map (getr (ms_regs ms6')) CLOB)) as E4 eqn:HE4.
assert (OLD4 : forall j, (j < 83)%nat -> ew E4 j = ew E3 j) by (img_try (intros j Hj; rewrite HE4; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp4 : bv_unsigned (ew E4 2) = sp0) by (img_try (rewrite OLD4 by ((img_case; cbv); img_lia); img_exact Usp3)).
assert (G3_4 : ew E4 3 = w64 (as_gp B)) by (img_try (rewrite OLD4 by ((img_case; cbv); img_lia); img_exact G3_3)).
assert (G4_4 : ew E4 4 = w64 (as_tp B)) by (img_try (rewrite OLD4 by ((img_case; cbv); img_lia); img_exact G4_3)).
assert (G12_4 : bv_unsigned (ew E4 12) = ap) by (img_try (rewrite OLD4 by ((img_case; cbv); img_lia); img_exact G12_3)).
assert (A34_4 : bv_unsigned (ew E4 34) = wp) by (img_try (rewrite OLD4 by ((img_case; cbv); img_lia); img_exact A34_3)).
assert (HAE4 : env_agree 32 EA E4)
by (img_try (rewrite HE4; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (img_exact HAE3)])).
clear HE4 HS6 VO6 SRA6' SHU6' Heff6'.
clear PAD6 DRA6' DHU6'.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E4 n_af6 n_st7 _ _ _ HS6' n_run7) HAI6').
intros W7 c7 _ HAI7 (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). cbn [cfg_model] in HAI7. clear HS6'.
rewrite ?wvb_wvb in HAI7 |- *.
assert (VO7 : VO B ly S W sp0 mem md MUT (ms_mem ms7) (with_vm_backing (m_vm_lazy md) mat7 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms7) mat7 VO6') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF7. intros Hin. destruct (vo_windows_sound E4 n_af6 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp4 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- intros x Hx1 Hx2. img_apply HFr7. intros Hin. destruct (vo_windows_sound E4 n_af6 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp4 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- img_apply (vf_band_present W E4 n_st7 ms7 sp0 HS7 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp4 ltac:(img_lia)). }
assert (BUFA7 : aview tfxsegs (w_H W) (ms_mem ms7) (wp) = Some 48).
{ rewrite <- BUFA6'. img_apply aview_eq_of. img_apply HFr7. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (vo_windows_sound E4 n_af6 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp4 Hin) as [Hw|Hw]; [img_try (unfold vf_band in Hw; GEO) | img_try (unfold vo_file, F_STDOUT, FILE_SZ in Hw; GEO)]. }
clear VO6' HF7 HFr7 BUFA6'.
pose proof (st_ok_add_cond tfxsegs E4 n_st7 _ BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (1 - BUFEND))) (SLit 0) HS7 ltac:(img_try (rewrite branch_geu_U, U_SLit; img_change (zcanon 0) with 0; img_apply Bool.negb_true_iff; img_apply Z.ltb_ge; pose proof (U_range E4 (SAlu ALU_SUB (SLit 0) (SOff 34 (1 - BUFEND)))); img_lia))) as HS7c.
img_change (YQ09.add_cond n_st7 (mkAC BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (1 - BUFEND))) (SLit 0))) with n_st7c in HS7c. clear HS7.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E4 n_st7c n_st8 _ _ _ HS7c n_run8) HAI7).
intros W8 c8 _ HAI8 (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). cbn [cfg_model] in HAI8. clear HS7c.
rewrite ?wvb_wvb in HAI8 |- *.
assert (VO8 : VO B ly S W sp0 mem md MUT (ms_mem ms8) (with_vm_backing (m_vm_lazy md) mat8 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms8) mat8 VO7) as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF8. intros Hin. destruct (vo_windows_sound E4 n_st7c sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp4 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- intros x Hx1 Hx2. img_apply HFr8. intros Hin. destruct (vo_windows_sound E4 n_st7c sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp4 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- img_apply (vf_band_present W E4 n_st8 ms8 sp0 HS8 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp4 ltac:(img_lia)). }
assert (BUFA8 : aview tfxsegs (w_H W) (ms_mem ms8) (wp) = Some 48).
{ rewrite <- BUFA7. img_apply aview_eq_of. img_apply HFr8. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (vo_windows_sound E4 n_st7c sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp4 Hin) as [Hw|Hw]; [img_try (unfold vf_band in Hw; GEO) | img_try (unfold vo_file, F_STDOUT, FILE_SZ in Hw; GEO)]. }
clear VO7 HF8 HFr8 BUFA7.
assert (SRA8' : range_addressable (aview tfxsegs (w_H W) (ms_mem ms8)) SHADOW_OFF (sp0 + PAD_OFF) 0) by (img_try (intros y Hy; img_lia)).
assert (SHU8' : 0 < 0 -> shadow_hull_vis (aview tfxsegs (w_H W) (ms_mem ms8)) (sp0 + PAD_OFF) 0) by (img_try (intros H0; img_lia)).
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_memcpy_ext B LAWS AMEMCPY W E4 n_st8 ms8 _ ly S sp0 n_r08 n_rest8 99 RA_FX OSP_FX
(SOff 34 1) (SOff 2 PAD_OFF) (SLit 0) (wp + 1) (sp0 + PAD_OFF) 0
HS8 ltac:(img_try (rewrite HBcode; img_refl)) ltac:(img_eqrefl_t) Usp4 G3_4 G4_4 ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t)
ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t)
ltac:(img_eqrefl_t) ltac:(img_try (cbn [sv_denot]; rewrite A34_4; img_refl)) ltac:(img_eqrefl_t) ltac:(img_try (cbn [sv_denot]; rewrite Usp4; img_refl)) ltac:(img_eqrefl_t) ltac:(img_refl)
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_lia)
ltac:(img_try (unfold RA_FX; img_lia)) ltac:(img_refl)
ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_try (GEO))
ltac:(img_try (left; unfold kLowMemEnd; GEO))
ltac:(img_try (first [left; unfold kLowMemEnd; GEO | eapply (vf_stack_amem B); [img_try (img_exact (proj1 VO8)) | img_try (img_exact Hstk) | img_try (img_exact HtopS) | img_try (GEO) | img_try (GEO)]]))
(vo_rest_disj E4 sp0 ap n_rest8 (wp + 1) 0 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_4 Hap1 Hsp44 ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_lia))
(vo_rest_ok E4 sp0 ap n_rest8 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_4 Hap1 Hap2)
(vo_rest_w E4 n_rest8 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VO8) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VO8)))
ltac:(img_try (intros a Ha; img_lia)) SRA8' SHU8'
ltac:(img_try (intros a Ha; img_lia)) ltac:(img_try (intros y Hy; img_lia)) ltac:(img_try (intros H0; img_lia))) HAI8).
intros W8' c8' _ HAI8' (-> & ms8' & mat8' & -> & HS8' & HAR8' & HP8' & Heff8' & Hfr8' & Hpm8'). cbn [cfg_model] in HAI8'.
rewrite wvb_wvb in HAI8', HAR8' |- *.
img_change (vf_after_icpt 99 n_st8 RA_FX OSP_FX 0 []) with n_af8 in HS8'.
assert (VO8' : VO B ly S W sp0 mem md MUT (ms_mem ms8') (with_vm_backing (m_vm_lazy md) mat8' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms8) _ (ms_mem ms8') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ ((wp + 1) <= a < (wp + 1) + 0))).
- img_exact VO8.
- img_exact HAR8'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat8' mat8 md). img_apply with_vm_backing_same.
- intros a [Ha|Ha]; [img_try (left; unfold vf_band, OSP_FX in *; img_lia) | img_try (right; unfold MUT, vo_mut; GEO)].
- intros a Hr Hna. img_apply Hfr8'; [img_try (img_exact Hr) | img_try (intros H'; img_apply Hna; left; img_exact H') | img_try (intros H'; img_apply Hna; right; img_exact H')].
- img_exact Hpm8'. }
assert (BUFA8' : aview tfxsegs (w_H W) (ms_mem ms8') (wp) = Some 48).
{ rewrite <- BUFA8. img_apply Hfr8'; [img_try (GEO) | img_try (GEO) | img_try (GEO)]. }
remember (havoc E4 99 (map (getr (ms_regs ms8')) CLOB)) as E5 eqn:HE5.
assert (OLD5 : forall j, (j < 99)%nat -> ew E5 j = ew E4 j) by (img_try (intros j Hj; rewrite HE5; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp5 : bv_unsigned (ew E5 2) = sp0) by (img_try (rewrite OLD5 by ((img_case; cbv); img_lia); img_exact Usp4)).
assert (G3_5 : ew E5 3 = w64 (as_gp B)) by (img_try (rewrite OLD5 by ((img_case; cbv); img_lia); img_exact G3_4)).
assert (G4_5 : ew E5 4 = w64 (as_tp B)) by (img_try (rewrite OLD5 by ((img_case; cbv); img_lia); img_exact G4_4)).
assert (G12_5 : bv_unsigned (ew E5 12) = ap) by (img_try (rewrite OLD5 by ((img_case; cbv); img_lia); img_exact G12_4)).
assert (A34_5 : bv_unsigned (ew E5 34) = wp) by (img_try (rewrite OLD5 by ((img_case; cbv); img_lia); img_exact A34_4)).
assert (HAE5 : env_agree 32 EA E5)
by (img_try (rewrite HE5; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (img_exact HAE4)])).
clear HE5 HS8 VO8 SRA8' SHU8' Heff8' BUFA8.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E5 n_af8 n_st9 _ _ _ HS8' n_run9) HAI8').
intros W9 c9 _ HAI9 (-> & ms9 & mat9 & -> & HS9 & HF9 & HFr9). cbn [cfg_model] in HAI9. clear HS8'.
rewrite ?wvb_wvb in HAI9 |- *.
assert (VO9 : VO B ly S W sp0 mem md MUT (ms_mem ms9) (with_vm_backing (m_vm_lazy md) mat9 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms9) mat9 VO8') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF9. intros Hin. destruct (vo_windows_sound E5 n_af8 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp5 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- intros x Hx1 Hx2. img_apply HFr9. intros Hin. destruct (vo_windows_sound E5 n_af8 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp5 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- img_apply (vf_band_present W E5 n_st9 ms9 sp0 HS9 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp5 ltac:(img_lia)). }
assert (BUFA9 : aview tfxsegs (w_H W) (ms_mem ms9) (wp) = Some 48).
{ rewrite <- BUFA8'. img_apply aview_eq_of. img_apply HFr9. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (vo_windows_sound E5 n_af8 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp5 Hin) as [Hw|Hw]; [img_try (unfold vf_band in Hw; GEO) | img_try (unfold vo_file, F_STDOUT, FILE_SZ in Hw; GEO)]. }
clear VO8' HF9 HFr9 BUFA8'.
pose proof (st_ok_add_cond tfxsegs E5 n_st9 _ BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (1 - BUFEND))) (SLit 1) HS9 ltac:(img_try (rewrite branch_geu_U, U_neg_off, U_SLit by (rewrite A34_5; unfold M64; img_lia); rewrite A34_5; img_change (zcanon 1) with 1; img_apply Bool.negb_true_iff; img_apply Z.ltb_ge; img_lia))) as HS9c.
img_change (YQ09.add_cond n_st9 (mkAC BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (1 - BUFEND))) (SLit 1))) with n_st9c in HS9c. clear HS9.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E5 n_st9c n_st10 _ _ _ HS9c n_run10) HAI9).
intros W10 c10 _ HAI10 (-> & ms10 & mat10 & -> & HS10 & HF10 & HFr10). cbn [cfg_model] in HAI10. clear HS9c.
rewrite ?wvb_wvb in HAI10 |- *.
assert (VO10 : VO B ly S W sp0 mem md MUT (ms_mem ms10) (with_vm_backing (m_vm_lazy md) mat10 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms10) mat10 VO9) as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF10. intros Hin. destruct (vo_windows_sound E5 n_st9c sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp5 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- intros x Hx1 Hx2. img_apply HFr10. intros Hin. destruct (vo_windows_sound E5 n_st9c sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp5 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- img_apply (vf_band_present W E5 n_st10 ms10 sp0 HS10 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp5 ltac:(img_lia)). }
assert (BUFA10 : aview tfxsegs (w_H W) (ms_mem ms10) (wp) = Some 48).
{ rewrite <- BUFA9. img_apply aview_eq_of. img_apply HFr10. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (vo_windows_sound E5 n_st9c sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp5 Hin) as [Hw|Hw]; [img_try (unfold vf_band in Hw; GEO) | img_try (unfold vo_file, F_STDOUT, FILE_SZ in Hw; GEO)]. }
clear VO9 HF10 HFr10 BUFA9.
pose proof HS10 as HSc10. destruct HSc10 as (_ & _ & _ & _ & _ & _ & _ & Hmem10 & _). cbn [restrict ms_mem] in Hmem10.
assert (NL10 : aview tfxsegs (w_H W) (ms_mem ms10) (84067 + D_20) = Some 10).
{ img_change (84067 + D_20) with ((84067 + D_20) + Z.of_nat 0).
img_apply (lit_buf_aview W E5 (ms_mem ms10) (ss_mem n_st10) (SLit (84067 + D_20)) (84067 + D_20) 1 [10] Hmem10 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_eqrefl_t) ltac:(img_try (repeat constructor; img_lia)) 0%nat ltac:(img_lia)). }
clear Hmem10.
destruct (vo_shadow_xfer B ly S W sp0 mem md wp (wp + 2) (ms_mem ms10) _ FMT_d 4 (84067 + D_20) 1 VO10 ltac:(img_lia) Hstk Hra_f Hhull_f
ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) ltac:(img_try (rewrite KHI; img_lia))) as [SRA10' SHU10'].
destruct (vo_shadow_xfer B ly S W sp0 mem md wp (wp + 2) (ms_mem ms10) _ STDOUT_BUFA STDOUT_BSZ (wp + 1) 1 VO10 ltac:(img_lia) Hstk Hra_b Hhull_b
ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) ltac:(img_try (rewrite KHI; img_lia))) as [DRA10' DHU10'].
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_memcpy_ext B LAWS AMEMCPY W E5 n_st10 ms10 _ ly S sp0 n_r010 n_rest10 115 RA_FX OSP_FX
(SOff 34 1) (SLit (84067 + D_20)) (SLit 1) (wp + 1) ((84067 + D_20)) 1
HS10 ltac:(img_try (rewrite HBcode; img_refl)) ltac:(img_eqrefl_t) Usp5 G3_5 G4_5 ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t)
ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t) ltac:(img_eqrefl_t)
ltac:(img_eqrefl_t) ltac:(img_try (cbn [sv_denot]; rewrite A34_5; img_refl)) ltac:(img_eqrefl_t) ltac:(img_refl) ltac:(img_eqrefl_t) ltac:(img_refl)
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_lia)
ltac:(img_try (unfold RA_FX; img_lia)) ltac:(img_refl)
ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_try (GEO))
ltac:(img_try (left; unfold kLowMemEnd; GEO))
ltac:(img_try (first [left; unfold kLowMemEnd; GEO | eapply (vf_stack_amem B); [img_try (img_exact (proj1 VO10)) | img_try (img_exact Hstk) | img_try (img_exact HtopS) | img_try (GEO) | img_try (GEO)]]))
(vo_rest_disj E5 sp0 ap n_rest10 (wp + 1) 1 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_5 Hap1 Hsp44 ltac:(img_try (GEO)) ltac:(img_try (GEO)) ltac:(img_lia))
(vo_rest_ok E5 sp0 ap n_rest10 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_5 Hap1 Hap2)
(vo_rest_w E5 n_rest10 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VO10) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VO10)))
ltac:(img_try (intros a Ha; replace a with (84067 + D_20) by img_lia; rewrite NL10; discriminate)) SRA10' SHU10'
ltac:(img_try (intros a Ha; split; [img_try (img_apply stdout_buf_writable; img_lia) | img_try (img_apply HBown; right; img_lia)])) ltac:(img_try (img_exact DRA10')) ltac:(img_try (img_exact DHU10'))) HAI10).
intros W10' c10' _ HAI10' (-> & ms10' & mat10' & -> & HS10' & HAR10' & HP10' & Heff10' & Hfr10' & Hpm10'). cbn [cfg_model] in HAI10'.
rewrite wvb_wvb in HAI10', HAR10' |- *.
img_change (vf_after_icpt 115 n_st10 RA_FX OSP_FX 0 []) with n_af10 in HS10'.
assert (VO10' : VO B ly S W sp0 mem md MUT (ms_mem ms10') (with_vm_backing (m_vm_lazy md) mat10' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms10) _ (ms_mem ms10') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ ((wp + 1) <= a < (wp + 1) + 1))).
- img_exact VO10.
- img_exact HAR10'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat10' mat10 md). img_apply with_vm_backing_same.
- intros a [Ha|Ha]; [img_try (left; unfold vf_band, OSP_FX in *; img_lia) | img_try (right; unfold MUT, vo_mut; GEO)].
- intros a Hr Hna. img_apply Hfr10'; [img_try (img_exact Hr) | img_try (intros H'; img_apply Hna; left; img_exact H') | img_try (intros H'; img_apply Hna; right; img_exact H')].
- img_exact Hpm10'. }
assert (BUFA10' : aview tfxsegs (w_H W) (ms_mem ms10') (wp) = Some 48).
{ rewrite <- BUFA10. img_apply Hfr10'; [img_try (GEO) | img_try (GEO) | img_try (GEO)]. }
assert (BUFB10' : aview tfxsegs (w_H W) (ms_mem ms10') (wp + 1) = Some 10).
{ replace (wp + 1) with (wp + 1 + 0) by img_lia. rewrite (Heff10' 0) by img_lia. rewrite Z.add_0_r. img_exact NL10. }
remember (havoc E5 115 (map (getr (ms_regs ms10')) CLOB)) as E6 eqn:HE6.
assert (OLD6 : forall j, (j < 115)%nat -> ew E6 j = ew E5 j) by (img_try (intros j Hj; rewrite HE6; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp6 : bv_unsigned (ew E6 2) = sp0) by (img_try (rewrite OLD6 by ((img_case; cbv); img_lia); img_exact Usp5)).
assert (G3_6 : ew E6 3 = w64 (as_gp B)) by (img_try (rewrite OLD6 by ((img_case; cbv); img_lia); img_exact G3_5)).
assert (G4_6 : ew E6 4 = w64 (as_tp B)) by (img_try (rewrite OLD6 by ((img_case; cbv); img_lia); img_exact G4_5)).
assert (G12_6 : bv_unsigned (ew E6 12) = ap) by (img_try (rewrite OLD6 by ((img_case; cbv); img_lia); img_exact G12_5)).
assert (A34_6 : bv_unsigned (ew E6 34) = wp) by (img_try (rewrite OLD6 by ((img_case; cbv); img_lia); img_exact A34_5)).
assert (HAE6 : env_agree 32 EA E6)
by (img_try (rewrite HE6; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (img_exact HAE5)])).
clear HE6 HS10 VO10 SRA10' SHU10' Heff10' BUFA10.
clear NL10 DRA10' DHU10'.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E6 n_af10 n_st11 _ _ _ HS10' n_run11) HAI10').
intros W11 c11 _ HAI11 (-> & ms11 & mat11 & -> & HS11 & HF11 & HFr11). cbn [cfg_model] in HAI11. clear HS10'.
rewrite ?wvb_wvb in HAI11 |- *.
assert (VO11 : VO B ly S W sp0 mem md MUT (ms_mem ms11) (with_vm_backing (m_vm_lazy md) mat11 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms11) mat11 VO10') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF11. intros Hin. destruct (vo_windows_sound E6 n_af10 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- intros x Hx1 Hx2. img_apply HFr11. intros Hin. destruct (vo_windows_sound E6 n_af10 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 (or_introl Hw)))].
- img_apply (vf_band_present W E6 n_st11 ms11 sp0 HS11 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 ltac:(img_lia)). }
assert (BUFA11 : aview tfxsegs (w_H W) (ms_mem ms11) (wp) = Some 48).
{ rewrite <- BUFA10'. img_apply aview_eq_of. img_apply HFr11. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (vo_windows_sound E6 n_af10 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 Hin) as [Hw|Hw]; [img_try (unfold vf_band in Hw; GEO) | img_try (unfold vo_file, F_STDOUT, FILE_SZ in Hw; GEO)]. }
assert (BUFB11 : aview tfxsegs (w_H W) (ms_mem ms11) (wp + 1) = Some 10).
{ rewrite <- BUFB10'. img_apply aview_eq_of. img_apply HFr11. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (vo_windows_sound E6 n_af10 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 Hin) as [Hw|Hw]; [img_try (unfold vf_band in Hw; GEO) | img_try (unfold vo_file, F_STDOUT, FILE_SZ in Hw; GEO)]. }
clear VO10' HF11 HFr11 BUFA10' BUFB10'.
eapply (SRr_srealizes tfxsegs W _
(fun W' c' => W' = W /\ exists mat', c' = mkCfg (mkst (ms_regs ms11) (v_jalr (getr (ms_regs ms11) 1) 0) (ms_mem ms11) (seg_rom tfxsegs))
(with_vm_backing (m_vm_lazy md) mat' md)) T); [ | img_try (img_exact HAI11) | ].
{ eapply (SRr_ret_at tfxsegs tfxmusl_tbl tfxmusl_tbl_ok Hwx W E6); [img_try (img_exact HS11) | img_refl | img_try ((try img_inst; img_case; vm_compute); img_refl) |].
intros mat'. rewrite wvb_wvb. split; [img_refl|]. exists mat'. img_refl. }
intros WR cR _ HAIR (-> & matR & ->). cbn [cfg_model] in HAIR.
destruct VO11 as (HAR9 & Hsbm9 & Hpb9 & Hfr9 & Hpm9).
rreg HS11 (1%bv : bv 5) Q1.
rewrite OLD6, OLD5, OLD4, OLD3, OLD2, OLD1 in Q1 by (img_try ((img_case; cbv); img_lia)). rewrite E0_1 in Q1.
pose proof (st_ok_restrict_reg tfxsegs (w_H W) E6 _ _ 10 HS11) as Q10. cbn [ms_regs restrict] in Q10.
match type of Q10 with _ = sv_denot _ ?v => let v' := img_ev constr:(v) in img_change v with v' in Q10 end. cbn [sv_denot] in Q10.
replace (v_jalr (getr (ms_regs ms11) 1) 0) with (w64 (raZ regs))
by (img_try (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; img_exact Hra)).
assert (SBMR : same_but_materialized (with_vm_backing (m_vm_lazy md) mat11 md) (with_vm_backing (m_vm_lazy md) matR md))
by (img_try (rewrite <- (wvb_collapse (m_vm_lazy md) matR mat11 md); img_apply with_vm_backing_same)).
pose proof (same_but_materialized_frame _ _ SBMR) as MF.
img_apply (HK (ms_regs ms11) (ms_mem ms11) (with_vm_backing (m_vm_lazy md) matR md)).
* img_apply (al_frame _ _ LAWS ly S W (ms_mem ms11) _ (ms_mem ms11) _ HAR9); [img_try (intros; img_refl) | img_try (intros a Hv; img_exact Hv) | img_try (img_apply MF) | img_try (img_apply MF) | img_try (img_apply MF) | img_try (img_exact (YE0v.hs_kept_refl _ _))].
* img_exact (aregs_preserved_of_st_ok _ E6 _ _ regs _ HS11 HAE6 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))).
* img_apply with_vm_backing_same.
* rewrite Q10. img_refl.
* destruct HS11 as (_ & _ & _ & _ & _ & _ & _ & Hmem11 & _).
split.
-- unfold ofile_is, stdout_fields1.
repeat img_apply Forall_cons; try img_apply Forall_nil;
(eapply (val_mem_of_lit E6 (mrestrict (w_H W) (ms_mem ms11)) (ss_mem n_st11) _ _ _ Hmem11); (try img_inst; img_case; vm_compute); img_refl).
-- img_exact (val_mem_of_chunk8 E6 (mrestrict (w_H W) (ms_mem ms11)) (ss_mem n_st11) 1%nat (F_STDOUT + 40) (SOff 34 2) (wp + 2) Hmem11
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try (cbn [sv_denot]; rewrite A34_6; img_refl)) ltac:(img_lia)).
* img_exact BUFA11.
* img_exact BUFB11.
* img_exact Hfr9.
* img_exact Hpm9.
* img_exact HAIR.
Qed.
End S.
End g.
