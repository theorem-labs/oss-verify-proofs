(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v YO0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE34 AF0l AE3e AE3f AE3g AE6g AE2p AE3i AE3h AF0m AE22 AF0x AE20 AE2y AE7f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma seg_rom_none_band : forall a, in_band_rw a -> seg_rom tfibsegs (Z_to_bv 64 a) = None.
Proof.
intros a Ha. apply AF0x.seg_rom_none_off. unfold AF0x.off_img, AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END.
unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha. lia.
Qed.
Definition F_STDOUT : Z := 0xa2668.
Definition STDOUT_BUFA : Z := 0x5f96a0.
Definition STDOUT_BSZ : Z := 1024.
Definition FMT_d : Z := 0x147ea.
Definition RA_PAD : Z := 0x94778.
Definition OSP_PC : Z := -912.
Definition PAD_OFF : Z := -736.
Definition stdout_fields0 : list (Z * N * Z) :=
[(0, 4%N, 5); (4, 4%N, 0); (8, 8%N, 0); (16, 8%N, 0); (24, 8%N, 0x92ba0); (32, 8%N, 0); (40, 8%N, 0); (48, 8%N, 0); (56, 8%N, 0); (64, 8%N, 0);
(72, 8%N, 0x93990); (80, 8%N, 0x92ce4); (88, 8%N, STDOUT_BUFA); (96, 8%N, STDOUT_BSZ); (104, 8%N, 0); (112, 8%N, 0); (120, 8%N, 1);
(128, 8%N, 0); (136, 4%N, 0); (140, 4%N, 0xffffffff); (144, 8%N, 10);
(152, 8%N, 0); (160, 8%N, 0); (168, 8%N, 0); (176, 8%N, 0); (184, 8%N, 0); (192, 8%N, 0); (200, 8%N, 0); (208, 8%N, 0);
(216, 8%N, 0); (224, 8%N, 0)].
Definition stdout_fields1 : list (Z * N * Z) :=
[(0, 4%N, 5); (4, 4%N, 0); (8, 8%N, 0); (16, 8%N, 0); (24, 8%N, 0x92ba0); (32, 8%N, STDOUT_BUFA + STDOUT_BSZ); (48, 8%N, 0);
(56, 8%N, STDOUT_BUFA); (64, 8%N, 0); (72, 8%N, 0x92cec); (80, 8%N, 0x92ce4); (88, 8%N, STDOUT_BUFA); (96, 8%N, STDOUT_BSZ);
(104, 8%N, 0); (112, 8%N, 0); (120, 8%N, 1); (128, 8%N, 0); (136, 4%N, 0xffffffff); (140, 4%N, 0xffffffff); (144, 4%N, 0xffffffff);
(152, 8%N, 0); (160, 8%N, 0); (168, 8%N, 0); (176, 8%N, 0); (184, 8%N, 0); (192, 8%N, 0); (200, 8%N, 0); (208, 8%N, 0);
(216, 8%N, 0); (224, 8%N, 0)].
Definition ofile_is (flds : list (Z * N * Z)) (m : word -> option byte) : Prop :=
Forall (fun f => match f with (o, n, v) => val_mem tfibsegs m (F_STDOUT + o) (N.to_nat n) v end) flds.
Definition stdout_pristine : (word -> option byte) -> Prop := ofile_is stdout_fields0.
Definition stdout_mid (wp : Z) (m : word -> option byte) : Prop :=
ofile_is stdout_fields1 m /\ val_mem tfibsegs m (F_STDOUT + 40) 8 wp.
Definition fo_chunks (flds : list (Z * N * Z)) : list YP09.chunk :=
map (fun f => match f with (o, n, v) => YP09.mkChunk (F_STDOUT + o) (CVal n (SLit v)) end) flds.
Definition vo_regions (fchunks : list YP09.chunk) : smem :=
[ YP09.mkRegion (Some 2%nat) (- VF_STK) 0 (- VF_STK) 0 [];
YP09.mkRegion None F_STDOUT (F_STDOUT + FILE_SZ) F_STDOUT (F_STDOUT + FILE_SZ) fchunks;
YP09.mkRegion None A_GOT_canary (A_GOT_canary + 8) 0 0 [YP09.mkChunk A_GOT_canary (CVal 8 (SLit A_canary))];
YP09.mkRegion None A_canary (A_canary + 8) 0 0 [YP09.mkChunk A_canary (CVal 8 (SOff 33 0))];
YP09.mkRegion (Some 12%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit 0))];
img_ro_region ].
Definition vo_sr : list sv := sr_set (sr_set sr_atoms (10%bv : bv 5) (SLit F_STDOUT)) (11%bv : bv 5) (SLit FMT_d).
Definition vo_facts0 : facts := mkFacts [ (2%nat, mkAF (2 ^ 44) (2 ^ 47) 4); (12%nat, mkAF (2 ^ 44) (2 ^ 47) 3) ] [] [].
Definition vo_facts1 : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 44) (2 ^ 47) 4); (12%nat, mkAF (2 ^ 44) (2 ^ 47) 3); (34%nat, mkAF STDOUT_BUFA (STDOUT_BUFA + STDOUT_BSZ - 2) 0) ] [] [].
Definition ss_vo0 : sstate := mkSS A_vfprintf vo_sr (vo_regions (fo_chunks stdout_fields0)) None vo_facts0.
Definition ss_vo1 : sstate :=
mkSS A_vfprintf vo_sr (vo_regions (YP09.mkChunk (F_STDOUT + 40) (CVal 8 (SOff 34 0)) :: fo_chunks stdout_fields1)) None vo_facts1.
Definition vo_file (a : Z) : Prop := F_STDOUT <= a < F_STDOUT + FILE_SZ.
Definition vo_mut (blo bhi : Z) (a : Z) : Prop := vo_file a \/ blo <= a < bhi.
Lemma stdout_img_bytes_ok : zallb (img_byte_ok tfibsegs) F_STDOUT (Z.to_nat FILE_SZ) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma stdout_buf_img_bytes_ok : zallb (img_byte_ok tfibsegs) STDOUT_BUFA (Z.to_nat STDOUT_BSZ) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma vo_mut_img : forall blo bhi a, STDOUT_BUFA <= blo -> bhi <= STDOUT_BUFA + STDOUT_BSZ ->
vo_mut blo bhi a -> img_byte_ok tfibsegs a = true.
Proof.
intros blo bhi a Hlo Hhi [Hf|Hb].
- unfold vo_file in Hf. exact (zallb_sound _ _ _ a stdout_img_bytes_ok ltac:(unfold FILE_SZ in *; lia)).
- exact (zallb_sound _ _ _ a stdout_buf_img_bytes_ok ltac:(unfold STDOUT_BSZ in *; lia)).
Qed.
Lemma vo_mut_dec : forall blo bhi a, vo_mut blo bhi a \/ ~ vo_mut blo bhi a.
Proof. intros blo bhi a. unfold vo_mut, vo_file. lia. Qed.
Section VO.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (sp0 : Z) (mem0 : word -> option byte) (md0 : Model).
Variable mut : Z -> Prop.
Hypothesis Hmut_img : forall a, mut a -> img_byte_ok tfibsegs a = true.
Hypothesis Hmut_dec : forall a, mut a \/ ~ mut a.
Hypothesis HFown : forall a, mut a -> ~ aowned B ly S a.
Hypothesis Hstk : ly_stk_lo ly + VF_STK <= sp0.
Hypothesis Htop : sp0 <= ly_stk_hi ly.
Definition VO (mem : word -> option byte) (md : Model) : Prop :=
AR tfibsegs B ly S W mem md /\ same_but_materialized md0 md /\
(forall a, vf_band sp0 a -> apresent (w_H W) mem a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_band sp0 a -> ~ mut a -> aview tfibsegs (w_H W) mem a = aview tfibsegs (w_H W) mem0 a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ mut a -> apresent (w_H W) mem0 a -> apresent (w_H W) mem a).
Lemma VO_init : AR tfibsegs B ly S W mem0 md0 -> (forall a, vf_band sp0 a -> apresent (w_H W) mem0 a) -> VO mem0 md0.
Proof.
intros HAR Hp. split; [exact HAR|]. split; [apply same_but_materialized_refl|]. split; [exact Hp|].
split; [intros; reflexivity | intros a _ _ Ha; exact Ha].
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
assert (HVF : VF_STK = 9104) by reflexivity.
assert (AVB : forall a, 0 <= a < 2 ^ 64 -> ~ vf_band sp0 a -> ~ mut a -> aview tfibsegs (w_H W) memB a = aview tfibsegs (w_H W) mem a).
{ intros a Hr H1 H2. apply aview_eq_of. apply HFr; rewrite unsigned_lit_small by lia; assumption. }
pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat)) as MF.
split; [|split; [|split; [exact HpbB | split]]].
- apply (al_frame _ _ LAWS ly S W mem md memB _ HAR).
+ intros a Hr Hown. apply AVB; [exact Hr | |].
* intros Hb. exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(unfold vf_band in Hb; lia) Hown).
* intros Hf. exact (HFown a Hf Hown).
+ assert (PV : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) mem a <> None -> aview tfibsegs (w_H W) memB a <> None).
{ intros a Hr Hv.
assert (CASE : vf_band sp0 a \/ mut a \/ (~ vf_band sp0 a /\ ~ mut a)).
{ destruct (Hmut_dec a) as [Hm|Hm]; [right; left; exact Hm|]. assert (D : vf_band sp0 a \/ ~ vf_band sp0 a) by (unfold vf_band; lia). tauto. }
destruct CASE as [Hin | [Hin | [Ho1 Ho2]]].
* apply aview_some_of_apresent. apply HpbB. exact Hin.
*
unfold aview, mbyte. destruct (mrestrict (w_H W) memB (Z_to_bv 64 a)) as [b|]; [cbn; discriminate|].
pose proof (Hmut_img a Hin) as Hb.
unfold img_byte_ok, img_byte in Hb. destruct (seg_rom tfibsegs (Z_to_bv 64 a)); [cbn; discriminate | discriminate Hb].
* rewrite AVB; assumption. }
intros a Hv. rewrite (aview_mod _ memB a). apply PV; [apply Z.mod_pos_bound; lia | rewrite <- aview_mod; exact Hv].
+ apply MF. + apply MF. + apply MF.
+
intros a Ha Hh. unfold YG0d.w64 in Hh. unfold YG0d.w64.     destruct (Hmut_dec a) as [Hmt|Hmt].
* exfalso. pose proof (Hmut_img a Hmt) as Hb. unfold img_byte_ok, img_byte in Hb. rewrite (seg_rom_none_band a Ha) in Hb. discriminate Hb.
* assert (CASE : vf_band sp0 a \/ ~ vf_band sp0 a) by (unfold vf_band; lia).
destruct CASE as [Hin|Hout]; [exfalso; destruct (Hpb a Hin) as [Hf _]; rewrite Hf in Hh; discriminate Hh|].
rewrite HF; [reflexivity | |]; rewrite unsigned_lit_small by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia); assumption.
- eapply same_but_materialized_trans; [exact Hsbm | apply with_vm_backing_same].
- intros a Hr H1 H2. rewrite AVB by assumption. apply Hfr; assumption.
- intros a Hr Hf Hp.
assert (CASE : vf_band sp0 a \/ ~ vf_band sp0 a) by (unfold vf_band; lia).
destruct CASE as [Hin | Hout]; [apply HpbB; exact Hin|].
destruct (Hpm a Hr Hf Hp) as [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite HF; [exact Hb| |]; rewrite unsigned_lit_small by lia; assumption.
Qed.
Lemma VO_splice : forall mem md memB mdB (Sx : Z -> Prop),
VO mem md ->
AR tfibsegs B ly S W memB mdB -> same_but_materialized md mdB ->
(forall a, Sx a -> vf_band sp0 a \/ mut a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Sx a -> aview tfibsegs (w_H W) memB a = aview tfibsegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) memB a) ->
VO memB mdB.
Proof.
intros mem md memB mdB Sx (HAR & Hsbm & Hpb & Hfr & Hpm) HARB HsbmB HSx HfrB HpmB.
split; [exact HARB|]. split; [eapply same_but_materialized_trans; [exact Hsbm | exact HsbmB]|].
split; [intros a Ha; apply HpmB; apply Hpb; exact Ha|]. split.
- intros a Hr H1 H2. rewrite HfrB; [apply Hfr; assumption | exact Hr | intros Hs; destruct (HSx a Hs) as [Hb|Hm]; [exact (H1 Hb) | exact (H2 Hm)]].
- intros a Hr Hf Hp. apply HpmB. apply Hpm; assumption.
Qed.
End VO.
Lemma vo_shadow_xfer : forall B ly S (W : world tfibsegs) sp0 mem0 md0 blo bhi mem md x0 m x n,
VO B ly S W sp0 mem0 md0 (vo_mut blo bhi) mem md -> bhi <= STDOUT_BUFA + STDOUT_BSZ -> ly_stk_lo ly + VF_STK <= sp0 ->
range_addressable (aview tfibsegs (w_H W) mem0) SHADOW_OFF x0 m -> shadow_hull_vis (aview tfibsegs (w_H W) mem0) x0 m ->
0 <= x0 -> x0 <= x -> x + n <= x0 + m -> x0 + m <= kHighMemEnd ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x n).
Proof.
intros B ly S W sp0 mem0 md0 blo bhi mem md x0 m x n (HAR & _ & _ & Hfr & _) Hbhi Hstk Hra Hh Hx0 Hx1 Hx2 Hx3.
assert (HVF : VF_STK = 9104) by reflexivity. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (SH : forall y, 0 <= y < kHighMemEnd -> forall s, shadow_addr y / 8 * 8 <= s < shadow_addr y / 8 * 8 + 8 ->
aview tfibsegs (w_H W) mem s = aview tfibsegs (w_H W) mem0 s).
{ intros y Hy s Hs. pose proof (shadow_addr_bounds y Hy) as [B1 B2].
apply Hfr; unfold vf_band, vo_mut, vo_file, F_STDOUT, FILE_SZ, STDOUT_BUFA, STDOUT_BSZ in *; unfold kLowMemEnd, kHighShadowEnd, kHighMemBeg in *; lia. }
split.
- intros y Hy. destruct (Hra y ltac:(lia)) as (v & Hv & Hok). exists v. split; [|exact Hok].
rewrite (SH y ltac:(lia)); [exact Hv|]. change (shadow_of_addr SHADOW_OFF y) with (shadow_addr y). lia.
- intros Hn s Hs.
assert (Hy : exists y, x <= y < x + n /\ shadow_addr y / 8 * 8 <= s < shadow_addr y / 8 * 8 + 8).
{ unfold shadow_addr in *.
destruct (Z_lt_le_dec s ((x + n - 1) / 8 + SHADOW_OFF)) as [Hlt|Hge].
+ exists (x + Z.max 0 ((s - SHADOW_OFF) * 8 - x)). split; [lia|]. lia.
+ exists (x + n - 1). lia. }
destruct Hy as (y & Hy1 & Hy2). rewrite (SH y ltac:(lia) s Hy2). apply Hh. unfold shadow_addr in *. lia.
Qed.
Definition vo_rest : smem := Eval vm_compute in (tl (vo_regions [])).
Lemma vo_rest_ok : forall E sp0 ap (rest : smem),
skeleton rest = skeleton vo_rest ->
bv_unsigned (ew E 12) = ap -> sp0 <= ap -> ap + 8 <= 2 ^ 47 ->
forall r, In r rest -> (YP09.r_base r = None /\ 0 <= YP09.r_lo r /\ YP09.r_hi r <= 2 ^ 43) \/
(YP09.r_base r = Some 12%nat /\ 0 <= YP09.r_lo r /\ bv_unsigned (ew E 12) + YP09.r_hi r <= 2 ^ 47 /\
sp0 <= bv_unsigned (ew E 12) + YP09.r_lo r).
Proof.
intros E sp0 ap rest Hsk H12 Hap1 Hap2 r Hr. pose proof (In_skel rest r Hr) as Hin. rewrite Hsk in Hin.
unfold vo_rest, skeleton in Hin. cbn in Hin. destruct r as [b lo hi wlo whi cs]. unfold skel in Hin. cbn in Hin.
cbn [YP09.r_base YP09.r_lo YP09.r_hi].
destruct Hin as [Hq|[Hq|[Hq|[Hq|[Hq|[]]]]]]; symmetry in Hq; injection Hq; intros; subst;
unfold F_STDOUT, FILE_SZ, A_GOT_canary, A_canary, IMG_RO_LO, IMG_RO_HI; first [left; repeat split; lia | right; repeat split; lia].
Qed.
Lemma vo_rest_w : forall E (rest : smem), skeleton rest = skeleton vo_rest ->
forall r a (m : word -> option byte), In r rest ->
base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r -> writable_at tfibsegs m a.
Proof.
intros E rest Hsk r a m Hr Ha. pose proof (In_skel rest r Hr) as Hin. rewrite Hsk in Hin.
unfold vo_rest, skeleton in Hin. cbn in Hin. destruct r as [b lo hi wlo whi cs]. unfold skel in Hin. cbn in Hin.
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
destruct Hin as [Hq|[Hq|[Hq|[Hq|[Hq|[]]]]]]; symmetry in Hq; injection Hq; intros; subst; cbn [base_val] in Ha; try lia.
unfold F_STDOUT, FILE_SZ in Ha. unfold writable_at.
apply (store_ok_all tfibsegs m 232 (Z_to_bv 64 F_STDOUT));
[rewrite unsigned_lit_small by (unfold F_STDOUT; lia); unfold F_STDOUT; cbn; lia
| apply store_ok_wseg; vm_compute; reflexivity
| rewrite !unsigned_lit_small by (unfold F_STDOUT in *; lia); unfold F_STDOUT in *; cbn; lia].
Qed.
Lemma vo_rest_disj : forall E sp0 ap (rest : smem) d n,
skeleton rest = skeleton vo_rest ->
bv_unsigned (ew E 12) = ap -> sp0 <= ap -> 2 ^ 44 <= sp0 ->
STDOUT_BUFA <= d -> d + n <= STDOUT_BUFA + STDOUT_BSZ -> 0 <= n ->
forall r, In r rest -> d + n <= base_val E (YP09.r_base r) + YP09.r_lo r \/ base_val E (YP09.r_base r) + YP09.r_hi r <= d.
Proof.
intros E sp0 ap rest d n Hsk H12 Hap Hsp Hd1 Hd2 Hn r Hr. pose proof (In_skel rest r Hr) as Hin. rewrite Hsk in Hin.
unfold vo_rest, skeleton in Hin. cbn in Hin. destruct r as [b lo hi wlo whi cs]. unfold skel in Hin. cbn in Hin.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
destruct Hin as [Hq|[Hq|[Hq|[Hq|[Hq|[]]]]]]; symmetry in Hq; injection Hq; intros; subst; cbn [base_val]; rewrite ?H12;
unfold F_STDOUT, FILE_SZ, A_GOT_canary, A_canary, IMG_RO_LO, IMG_RO_HI, STDOUT_BUFA, STDOUT_BSZ in *; lia.
Qed.
Lemma stdout_buf_writable : forall (m : word -> option byte) a,
STDOUT_BUFA <= a < STDOUT_BUFA + STDOUT_BSZ -> writable_at tfibsegs m a.
Proof.
intros m a Ha. unfold writable_at, STDOUT_BUFA, STDOUT_BSZ in *.
apply (store_ok_all tfibsegs m 1024 (Z_to_bv 64 STDOUT_BUFA));
[rewrite unsigned_lit_small by (unfold STDOUT_BUFA; lia); unfold STDOUT_BUFA; cbn; lia
| apply store_ok_wseg; vm_compute; reflexivity
| rewrite !unsigned_lit_small by (unfold STDOUT_BUFA in *; lia); unfold STDOUT_BUFA in *; cbn; lia].
Qed.
Definition vo_windows_ok (ss : sstate) : bool :=
forallb (fun t => band_winb t || win_eqb t (None, F_STDOUT, F_STDOUT + FILE_SZ) || (snd t <=? snd (fst t)))
(windows (ss_mem ss)).
Lemma vo_windows_sound : forall E ss sp0 a,
vo_windows_ok ss = true -> bv_unsigned (ew E 2) = sp0 ->
in_wrange E (ss_mem ss) a -> vf_band sp0 a \/ vo_file a.
Proof.
intros E ss sp0 a Hb Hsp Hin.
destruct (in_wrange_windows E _ a Hin) as (b & lo & hi & Ht & Hr).
unfold vo_windows_ok in Hb. rewrite forallb_forall in Hb. specialize (Hb _ Ht).
apply orb_prop in Hb as [Hb|Hb]; [apply orb_prop in Hb as [Hb|Hb]|].
- unfold band_winb in Hb. destruct b as [[|[|[|n]]]|]; try discriminate Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.eqb_eq in H1. apply Z.leb_le in H2. subst lo.
cbn [base_val] in Hr. rewrite Hsp in Hr. left. unfold vf_band. lia.
- apply win_eqb_eq in Hb. injection Hb as -> -> ->. cbn [base_val] in Hr. right. unfold vo_file. lia.
- cbn [fst snd] in Hb. apply Z.leb_le in Hb. lia.
Qed.
Lemma vo_entry0 : forall (W : world tfibsegs) regs mem ap cval,
2 ^ 44 <= spZ regs -> spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
(forall a, spZ regs - VF_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 F_STDOUT -> getr regs 11 = w64 FMT_d -> getr regs 12 = w64 ap ->
spZ regs <= ap -> ap + 8 <= 2 ^ 47 -> ap mod 8 = 0 ->
val_mem tfibsegs (mrestrict (w_H W) mem) ap 8 0 ->
stdout_pristine (mrestrict (w_H W) mem) ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
ro_img (mrestrict (w_H W) mem) ->
st_ok tfibsegs (Ereg regs [Z_to_bv 64 0; Z_to_bv 64 cval]) ss_vo0
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_vfprintf) mem (seg_rom tfibsegs))).
Proof.
intros W regs mem ap cval Hsp1 Hsp2 Hal Hpres H10 H11 H12 Hap1 Hap2 Hap8 Harg HF Hgot Hcan Hcv Hro.
rewrite restrict_mkst_fx. unfold ss_vo0.
set (E := Ereg regs [Z_to_bv 64 0; Z_to_bv 64 cval]).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E12 : bv_unsigned (ew E 12) = ap) by (subst E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl), H12; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 0) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 cval) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (HVF : VF_STK = 9104) by reflexivity.
apply (entry_st_ok_full tfibsegs); change (Ereg regs [Z_to_bv 64 0; Z_to_bv 64 cval]) with E.
- unfold vo_sr. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros Hx; discriminate Hx | rewrite H10; reflexivity]
| intros Hx; discriminate Hx | rewrite H11; reflexivity].
- vm_compute. reflexivity.
- unfold vo_regions. repeat apply Forall_cons; try apply Forall_nil.
+ apply (region_ok_stack tfibsegs E _ 2 (spZ regs) (- VF_STK)); [exact E2 | lia | lia |].
intros a Ha. apply apresent_writable. apply Hpres. lia.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
unfold F_STDOUT, FILE_SZ. split; [lia|]. split; [lia|]. split.
* intros o Ho. rewrite Z.add_0_l. unfold writable_at.
apply (store_ok_all tfibsegs (mrestrict (w_H W) mem) 232 (Z_to_bv 64 F_STDOUT));
[rewrite unsigned_lit_small by (unfold F_STDOUT; lia); unfold F_STDOUT; cbn; lia
| apply store_ok_wseg; vm_compute; reflexivity
| rewrite !unsigned_lit_small by (unfold F_STDOUT in *; lia); unfold F_STDOUT in *; cbn; lia].
* unfold fo_chunks, stdout_fields0. cbn [map].
unfold stdout_pristine, ofile_is, stdout_fields0 in HF.
repeat match type of HF with Forall _ (_ :: _) =>
let h := fresh "HFf" in pose proof (Forall_inv HF) as h; cbn beta iota in h; apply Forall_inv_tail in HF end.
repeat apply Forall_cons; try apply Forall_nil;
(eapply (chunk_ok_val tfibsegs E _ 0); [reflexivity | unfold STDOUT_BUFA, STDOUT_BSZ; zside | zside | rewrite Z.add_0_l; unfold F_STDOUT, STDOUT_BUFA, STDOUT_BSZ in *; assumption]).
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
unfold A_GOT_canary. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 0); [reflexivity | unfold A_canary; zside | zside |].
rewrite Z.add_0_l. exact Hgot.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
unfold A_canary. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 0 _ 8 _ cval); [| zside | zside | rewrite Z.add_0_l; exact Hcan].
cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E12. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ ap 0 8 _ 0); [reflexivity | zside | zside | rewrite Z.add_0_r; exact Harg].
+ apply Hro.
- apply pairwise_disjoint_of_extents. unfold vo_regions, img_ro_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E12.
unfold F_STDOUT, FILE_SZ, A_GOT_canary, A_canary, IMG_RO_LO, IMG_RO_HI.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I].
cbn [vo_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2, E12.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. repeat split; try lia.
Qed.
Lemma vo_entry1 : forall (W : world tfibsegs) regs mem ap cval wp,
2 ^ 44 <= spZ regs -> spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
(forall a, spZ regs - VF_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 F_STDOUT -> getr regs 11 = w64 FMT_d -> getr regs 12 = w64 ap ->
spZ regs <= ap -> ap + 8 <= 2 ^ 47 -> ap mod 8 = 0 ->
val_mem tfibsegs (mrestrict (w_H W) mem) ap 8 0 ->
stdout_mid wp (mrestrict (w_H W) mem) -> STDOUT_BUFA <= wp <= STDOUT_BUFA + STDOUT_BSZ - 2 ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
ro_img (mrestrict (w_H W) mem) ->
st_ok tfibsegs (Ereg regs [Z_to_bv 64 0; Z_to_bv 64 cval; Z_to_bv 64 wp]) ss_vo1
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_vfprintf) mem (seg_rom tfibsegs))).
Proof.
intros W regs mem ap cval wp Hsp1 Hsp2 Hal Hpres H10 H11 H12 Hap1 Hap2 Hap8 Harg [HF Hwp] Hwpr Hgot Hcan Hcv Hro.
rewrite restrict_mkst_fx. unfold ss_vo1.
set (E := Ereg regs [Z_to_bv 64 0; Z_to_bv 64 cval; Z_to_bv 64 wp]).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E12 : bv_unsigned (ew E 12) = ap) by (subst E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl), H12; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 0) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 cval) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 wp) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (HVF : VF_STK = 9104) by reflexivity.
apply (entry_st_ok_full tfibsegs); change (Ereg regs [Z_to_bv 64 0; Z_to_bv 64 cval; Z_to_bv 64 wp]) with E.
- unfold vo_sr. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros Hx; discriminate Hx | rewrite H10; reflexivity]
| intros Hx; discriminate Hx | rewrite H11; reflexivity].
- vm_compute. reflexivity.
- unfold vo_regions. repeat apply Forall_cons; try apply Forall_nil.
+ apply (region_ok_stack tfibsegs E _ 2 (spZ regs) (- VF_STK)); [exact E2 | lia | lia |].
intros a Ha. apply apresent_writable. apply Hpres. lia.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
unfold F_STDOUT, FILE_SZ. split; [lia|]. split; [lia|]. split.
* intros o Ho. rewrite Z.add_0_l. unfold writable_at.
apply (store_ok_all tfibsegs (mrestrict (w_H W) mem) 232 (Z_to_bv 64 F_STDOUT));
[rewrite unsigned_lit_small by (unfold F_STDOUT; lia); unfold F_STDOUT; cbn; lia
| apply store_ok_wseg; vm_compute; reflexivity
| rewrite !unsigned_lit_small by (unfold F_STDOUT in *; lia); unfold F_STDOUT in *; cbn; lia].
* unfold fo_chunks, stdout_fields1. cbn [map].
unfold ofile_is, stdout_fields1 in HF.
repeat match type of HF with Forall _ (_ :: _) =>
let h := fresh "HFf" in pose proof (Forall_inv HF) as h; cbn beta iota in h; apply Forall_inv_tail in HF end.
apply Forall_cons.
{ eapply (chunk_ok_val tfibsegs E _ 0 _ 8 _ wp); [| unfold STDOUT_BUFA, STDOUT_BSZ in *; zside | zside | rewrite Z.add_0_l; exact Hwp].
cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
repeat apply Forall_cons; try apply Forall_nil;
(eapply (chunk_ok_val tfibsegs E _ 0); [reflexivity | unfold STDOUT_BUFA, STDOUT_BSZ; zside | zside | rewrite Z.add_0_l; unfold F_STDOUT, STDOUT_BUFA, STDOUT_BSZ in *; assumption]).
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
unfold A_GOT_canary. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 0); [reflexivity | unfold A_canary; zside | zside |].
rewrite Z.add_0_l. exact Hgot.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
unfold A_canary. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 0 _ 8 _ cval); [| zside | zside | rewrite Z.add_0_l; exact Hcan].
cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E12. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ ap 0 8 _ 0); [reflexivity | zside | zside | rewrite Z.add_0_r; exact Harg].
+ apply Hro.
- apply pairwise_disjoint_of_extents. unfold vo_regions, img_ro_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E12.
unfold F_STDOUT, FILE_SZ, A_GOT_canary, A_canary, IMG_RO_LO, IMG_RO_HI.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I].
cbn [vo_facts1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2, E12, E34, unsigned_lit_small by (unfold STDOUT_BUFA, STDOUT_BSZ in *; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r. repeat split; try lia.
Qed.
Lemma srz_sym_ioctl_enotty : forall (W : world tfibsegs) E ss ms model fd ch T,
AI tfibsegs (w_H W) (w_A W) model ->
st_ok_ecall tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
bv_unsigned (sv_denot E (sr_get (ss_regs ss) 17)) = 29 ->
sv_denot E (sr_get (ss_regs ss) 10) = fd -> fdchan fd ch model -> fd32 fd = fd ->
cmd32 (sv_denot E (sr_get (ss_regs ss) 11)) = TIOCGWINSZ ->
(forall ms', st_ok tfibsegs E (resume ss (SLit (2 ^ 64 - 25)) (ss_mem ss) (ss_facts ss)) (restrict (w_H W) ms') ->
ms_mem ms' = ms_mem ms -> srealizes tfibsegs (mkCfg ms' model) T) ->
srealizes tfibsegs (mkCfg ms model) T.
Proof.
intros W E ss ms model fd ch T HAI HS Hrv H17 H10 [Hlk _] H32 H11 Hk.
destruct (st_ok_ecall_shape_r tfibsegs (w_H W) E ss ms HS Hrv) as (regs & mem & -> & Hregs & Hmem & HG).
cbn [ms_mem pend_at] in Hk.
eapply (srz_ioctl_winsz_lazy tfibsegs (w_H W) (w_A W) regs _ mem (seg_rom tfibsegs) model fd _ T HAI).
- rewrite (Hregs 17%bv). exact H17.
- rewrite (Hregs 10%bv). exact H10.
- exact H32.
- exact Hlk.
- intros rd wr; discriminate.
- rewrite (Hregs 11%bv). exact H11.
- apply (Hk (mkst (regupd regs 10 (errno_ret ENOTTY)) (v_addi (Z_to_bv 64 (ss_pc ss)) 4) mem (seg_rom tfibsegs))); [|reflexivity].
rewrite restrict_mkst_fx.
replace (errno_ret ENOTTY) with (sv_denot E (SLit (2 ^ 64 - 25))) by (apply bv_eq; vm_compute; reflexivity).
apply st_ok_resume_sv; auto.
Qed.
Definition o_st1 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL ss_vo0).
Definition o_af1 : sstate := Eval vm_compute in vf_after_icpt 34 o_st1 RA_FX OSP_FX 0 [].
Definition o_st2 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL o_af1).
Definition o_af2 : sstate := Eval vm_compute in vf_after_icpt 50 o_st2 RA_FX OSP_FX 0 [].
Definition o_st3 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL o_af2).
Definition o_af3 : sstate := Eval vm_compute in vf_after_icpt 66 o_st3 RA_PAD OSP_PC PAD_OFF (repeat 48 1%nat).
Definition o_st4 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL o_af3).
Definition o_af4 : sstate := Eval vm_compute in vf_after_icpt 82 o_st4 RA_FX OSP_FX 0 [].
Definition o_st5 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL o_af4).
Definition o_af5 : sstate := Eval vm_compute in vf_after_icpt 98 o_st5 RA_FX OSP_FX 0 [].
Definition o_st6 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL o_af5).
Definition o_af6 : sstate := Eval vm_compute in resume o_st6 (SLit (2 ^ 64 - 25)) (ss_mem o_st6) (ss_facts o_st6).
Definition o_st7 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL o_af6).
Definition o_af7 : sstate := Eval vm_compute in wl_after o_st7 0 (-1120) 114.
Definition o_st8 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL o_af7).
Definition o_af8 : sstate := Eval vm_compute in vf_after_icpt 125 o_st8 RA_FX OSP_FX 0 [].
Definition o_st9 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL o_af8).
Definition o_r01 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem o_st1).
Definition o_rest1 : smem := Eval vm_compute in tl (ss_mem o_st1).
Definition o_r02 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem o_st2).
Definition o_rest2 : smem := Eval vm_compute in tl (ss_mem o_st2).
Definition o_r03 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem o_st3).
Definition o_rest3 : smem := Eval vm_compute in tl (ss_mem o_st3).
Definition o_r04 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem o_st4).
Definition o_rest4 : smem := Eval vm_compute in tl (ss_mem o_st4).
Definition o_r05 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem o_st5).
Definition o_rest5 : smem := Eval vm_compute in tl (ss_mem o_st5).
Definition o_r08 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem o_st8).
Definition o_rest8 : smem := Eval vm_compute in tl (ss_mem o_st8).
Lemma o_run1 : sym_runN tfibsegs tfibmusl_tbl FUEL ss_vo0 = (o_st1, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma o_run2 : sym_runN tfibsegs tfibmusl_tbl FUEL o_af1 = (o_st2, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma o_run3 : sym_runN tfibsegs tfibmusl_tbl FUEL o_af2 = (o_st3, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma o_run4 : sym_runN tfibsegs tfibmusl_tbl FUEL o_af3 = (o_st4, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma o_run5 : sym_runN tfibsegs tfibmusl_tbl FUEL o_af4 = (o_st5, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma o_run6 : sym_runN tfibsegs tfibmusl_tbl FUEL o_af5 = (o_st6, RS_ecall). Proof. vm_compute. reflexivity. Qed.
Lemma o_run7 : sym_runN tfibsegs tfibmusl_tbl FUEL o_af6 = (o_st7, RS_ecall). Proof. vm_compute. reflexivity. Qed.
Lemma o_run8 : sym_runN tfibsegs tfibmusl_tbl FUEL o_af7 = (o_st8, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma o_run9 : sym_runN tfibsegs tfibmusl_tbl FUEL o_af8 = (o_st9, RS_stopped (SR_jalr (SOff 1 0))). Proof. vm_compute. reflexivity. Qed.
Definition BUFEND : Z := STDOUT_BUFA + STDOUT_BSZ.
Definition fx_cond (d l : Z) : acond := mkAC BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (d - BUFEND))) (SLit l).
Definition n_st1 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL ss_vo1).
Definition n_st1c : sstate := Eval vm_compute in YP06.add_cond n_st1 (fx_cond 0 0).
Definition n_st2 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL n_st1c).
Definition n_af2 : sstate := Eval vm_compute in vf_after_icpt 35 n_st2 RA_FX OSP_FX 0 [].
Definition n_st3 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL n_af2).
Definition n_af3 : sstate := Eval vm_compute in vf_after_icpt 51 n_st3 RA_FX OSP_FX 0 [].
Definition n_st4 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL n_af3).
Definition n_af4 : sstate := Eval vm_compute in vf_after_icpt 67 n_st4 RA_PAD OSP_PC PAD_OFF (repeat 48 1%nat).
Definition n_st5 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL n_af4).
Definition n_st5c : sstate := Eval vm_compute in YP06.add_cond n_st5 (fx_cond 0 1).
Definition n_st6 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL n_st5c).
Definition n_af6 : sstate := Eval vm_compute in vf_after_icpt 83 n_st6 RA_FX OSP_FX 0 [].
Definition n_st7 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL n_af6).
Definition n_st7c : sstate := Eval vm_compute in YP06.add_cond n_st7 (fx_cond 1 0).
Definition n_st8 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL n_st7c).
Definition n_af8 : sstate := Eval vm_compute in vf_after_icpt 99 n_st8 RA_FX OSP_FX 0 [].
Definition n_st9 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL n_af8).
Definition n_st9c : sstate := Eval vm_compute in YP06.add_cond n_st9 (fx_cond 1 1).
Definition n_st10 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL n_st9c).
Definition n_af10 : sstate := Eval vm_compute in vf_after_icpt 115 n_st10 RA_FX OSP_FX 0 [].
Definition n_st11 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL n_af10).
Definition n_r02 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem n_st2).
Definition n_rest2 : smem := Eval vm_compute in tl (ss_mem n_st2).
Definition n_r03 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem n_st3).
Definition n_rest3 : smem := Eval vm_compute in tl (ss_mem n_st3).
Definition n_r04 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem n_st4).
Definition n_rest4 : smem := Eval vm_compute in tl (ss_mem n_st4).
Definition n_r06 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem n_st6).
Definition n_rest6 : smem := Eval vm_compute in tl (ss_mem n_st6).
Definition n_r08 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem n_st8).
Definition n_rest8 : smem := Eval vm_compute in tl (ss_mem n_st8).
Definition n_r010 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem n_st10).
Definition n_rest10 : smem := Eval vm_compute in tl (ss_mem n_st10).
Lemma n_run1 : sym_runN tfibsegs tfibmusl_tbl FUEL ss_vo1 = (n_st1, RS_stopped (SR_branch BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (0 - BUFEND))) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Lemma n_run2 : sym_runN tfibsegs tfibmusl_tbl FUEL n_st1c = (n_st2, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma n_run3 : sym_runN tfibsegs tfibmusl_tbl FUEL n_af2 = (n_st3, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma n_run4 : sym_runN tfibsegs tfibmusl_tbl FUEL n_af3 = (n_st4, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma n_run5 : sym_runN tfibsegs tfibmusl_tbl FUEL n_af4 = (n_st5, RS_stopped (SR_branch BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (0 - BUFEND))) (SLit 1))). Proof. vm_compute. reflexivity. Qed.
Lemma n_run6 : sym_runN tfibsegs tfibmusl_tbl FUEL n_st5c = (n_st6, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma n_run7 : sym_runN tfibsegs tfibmusl_tbl FUEL n_af6 = (n_st7, RS_stopped (SR_branch BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (1 - BUFEND))) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Lemma n_run8 : sym_runN tfibsegs tfibmusl_tbl FUEL n_st7c = (n_st8, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma n_run9 : sym_runN tfibsegs tfibmusl_tbl FUEL n_af8 = (n_st9, RS_stopped (SR_branch BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (1 - BUFEND))) (SLit 1))). Proof. vm_compute. reflexivity. Qed.
Lemma n_run10 : sym_runN tfibsegs tfibmusl_tbl FUEL n_st9c = (n_st10, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma n_run11 : sym_runN tfibsegs tfibmusl_tbl FUEL n_af10 = (n_st11, RS_stopped (SR_jalr (SOff 1 0))). Proof. vm_compute. reflexivity. Qed.
Definition find_chunk8 (rs : smem) (i : nat) (off : Z) : option sv :=
match nth_error rs i with
| Some r => match YP09.r_base r with
| None => match List.find (fun c => YP09.c_off c =? off) (YP09.r_chunks r) with
| Some (YP09.mkChunk _ (CVal n e)) => if (n =? 8)%N then Some e else None
| _ => None
end
| Some _ => None
end
| None => None
end.
Lemma val_mem_of_chunk8 : forall E (m : word -> option byte) (rs : smem) i off e v,
mem_ok tfibsegs E m rs -> find_chunk8 rs i off = Some e ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
val_mem tfibsegs m off 8 v.
Proof.
intros E m rs i off e v (Hwf & Hrs & Hpd) Hf He Hv. unfold find_chunk8 in Hf.
destruct (nth_error rs i) as [r|] eqn:Hi; [|discriminate].
destruct (YP09.r_base r) as [b|] eqn:Hb; [discriminate|].
destruct (List.find (fun c => YP09.c_off c =? off) (YP09.r_chunks r)) as [[co cv]|] eqn:Hfd; [|discriminate].
destruct cv as [n e'| | |]; try discriminate. destruct (N.eqb_spec n 8) as [->|Hn]; [|discriminate].
injection Hf as ->.
apply find_some in Hfd as [Hin Hoff]. apply Z.eqb_eq in Hoff. cbn [YP09.c_off] in Hoff. subst co.
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. rewrite Hb in Hck. cbn [base_val] in Hck.
rewrite <- (Z.add_0_l off). apply (val_of_chunk_ok tfibsegs E m 0 off 8 e v Hck He); cbn; lia.
Qed.
Local Ltac GEO := unfold FMT_d, PAD_OFF, OSP_FX, OSP_PC, RA_FX, STDOUT_BUFA, STDOUT_BSZ, F_STDOUT, FILE_SZ, BUFEND in *; lia.
Section S.
Variable B : asyms.
Hypothesis TL : TfibSyms B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Hypothesis AMEMSET : aintrin_realizes tfibsegs B OSet (pc_wrap_memset (as_code B)).
Let HBcode := ts_code B TL.
Theorem tfib_vfprintf_stdout_first : forall ly S (W : world tfibsegs) regs mem md ch ap cval T,
ecall_pre tfibsegs B ly S W regs mem md ->
2 ^ 44 <= spZ regs -> ly_stk_lo ly + VF_STK <= spZ regs ->
(forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) ->
getr regs 10 = w64 F_STDOUT -> getr regs 11 = w64 FMT_d -> getr regs 12 = w64 ap ->
spZ regs <= ap -> ap + 8 <= 2 ^ 47 -> ap mod 8 = 0 ->
val_mem tfibsegs (mrestrict (w_H W) mem) ap 8 0 ->
stdout_pristine (mrestrict (w_H W) mem) ->
(forall a, vo_file a \/ STDOUT_BUFA <= a < STDOUT_BUFA + STDOUT_BSZ -> ~ aowned B ly S a) ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
ro_img (mrestrict (w_H W) mem) ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF STDOUT_BUFA STDOUT_BSZ ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) STDOUT_BUFA STDOUT_BSZ ->
fdchan (Z_to_bv 64 1) ch md -> AI tfibsegs (w_H W) (w_A W) md ->
(forall regs' mem' md',
AR tfibsegs B ly S W mem' md' -> aregs_preserved regs regs' -> same_but_materialized md md' ->
getr regs' 10 = w64 2 ->
stdout_mid STDOUT_BUFA (mrestrict (w_H W) mem') ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_band (spZ regs) a -> ~ vo_mut STDOUT_BUFA (STDOUT_BUFA + 1) a ->
aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vo_mut STDOUT_BUFA (STDOUT_BUFA + 1) a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
AI tfibsegs (w_H W) (w_A W) md' ->
srealizes tfibsegs (cfg_at tfibsegs (raZ regs) regs' mem' md') T) ->
srealizes tfibsegs (cfg_at tfibsegs A_vfprintf regs mem md) (t_emit (map (WriteEv ch) (map (Z_to_bv 8) [48; 10])) T).
Proof.
intros ly S W regs mem md ch ap cval T HPRE Hsp44 Hstk Hpres Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg
HFP HBown Hgot Hcan Hcv Hro Hra_b Hhull_b Hch HAI0 HK.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity. assert (HVF : VF_STK = 9104) by reflexivity.
assert (HFF : F_STDOUT = 665192) by reflexivity. assert (HFS : FILE_SZ = 232) by reflexivity.
assert (HBF : STDOUT_BUFA = 6264480) by reflexivity. assert (HBS : STDOUT_BSZ = 1024) by reflexivity.
assert (HFD : FMT_d = 83946) by reflexivity. assert (HPO : PAD_OFF = -736) by reflexivity. assert (HOX : OSP_FX = -976) by reflexivity.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by reflexivity.
set (sp0 := spZ regs) in *. assert (HtopS : sp0 < kHighMemEnd) by (rewrite KHI; lia).
assert (Hsp47 : sp0 <= 2 ^ 47) by lia.
set (MUT := vo_mut STDOUT_BUFA (STDOUT_BUFA + 1)) in *.
assert (MUTimg : forall a, MUT a -> img_byte_ok tfibsegs a = true) by (intros a Ha; apply (vo_mut_img STDOUT_BUFA (STDOUT_BUFA + 1) a); [lia | unfold STDOUT_BSZ; lia | exact Ha]).
assert (MUTdec : forall a, MUT a \/ ~ MUT a) by (intros a; apply vo_mut_dec).
assert (HFownM : forall a, MUT a -> ~ aowned B ly S a) by (intros a [Ha|Ha]; apply HBown; [left; exact Ha | right; unfold STDOUT_BSZ; lia]).
unfold cfg_at. change (w64 A_vfprintf) with (Z_to_bv 64 A_vfprintf).
pose proof (vo_entry0 W regs mem ap cval Hsp44 Hsp47 Hal16 ltac:(intros a Ha; apply Hpres; exact Ha) Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg
HFP Hgot Hcan Hcv Hro) as HS0.
set (EL := [Z_to_bv 64 0; Z_to_bv 64 cval]) in *.
remember (Ereg regs EL) as E0 eqn:HE0.
assert (EE : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E0 i = getr regs r)
by (intros i r Hi; rewrite HE0; exact (ew_Ereg_nat regs _ i r Hi)).
pose proof (EE 1%nat (1%bv : bv 5) eq_refl) as E0_1.
assert (Usp0 : bv_unsigned (ew E0 2) = sp0) by (rewrite (EE 2%nat (2%bv : bv 5) eq_refl); reflexivity).
assert (G3_0 : ew E0 3 = w64 (as_gp B)) by (rewrite (EE 3%nat (3%bv : bv 5) eq_refl); exact Hgp).
assert (G4_0 : ew E0 4 = w64 (as_tp B)) by (rewrite (EE 4%nat (4%bv : bv 5) eq_refl); exact Htp).
assert (G12_0 : bv_unsigned (ew E0 12) = ap) by (rewrite (EE 12%nat (12%bv : bv 5) eq_refl), Ha2; apply unsigned_lit_small; lia).
assert (HAE0 : env_agree 32 (Ereg regs EL) E0) by (rewrite HE0; split; [intros i Hi; reflexivity | reflexivity]).
set (EA := Ereg regs EL) in *.
clear HE0 EE.
pose proof (VO_init B ly S W sp0 mem md MUT HAR Hpres) as VO0.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E0 ss_vo0 o_st1 _ _ _ HS0 o_run1) HAI0).
intros W1 c1 _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [cfg_model] in HAI1. clear HS0.
rewrite ?wvb_wvb in HAI1 |- *.
assert (VO1 : VO B ly S W sp0 mem md MUT (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms1) mat1 VO0) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF1. intros Hin. destruct (vo_windows_sound E0 ss_vo0 sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr1. intros Hin. destruct (vo_windows_sound E0 ss_vo0 sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E0 o_st1 ms1 sp0 HS1 ltac:(vm_compute; reflexivity) Usp0 ltac:(lia)). }
clear VO0 HF1 HFr1.
assert (SRA1' : range_addressable (aview tfibsegs (w_H W) (ms_mem ms1)) SHADOW_OFF FMT_d 0) by (intros y Hy; lia).
assert (SHU1' : 0 < 0 -> shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms1)) FMT_d 0) by (intros H0; lia).
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy_ext B LAWS AMEMCPY W E0 o_st1 ms1 _ ly S sp0 o_r01 o_rest1 34 RA_FX OSP_FX
(SLit STDOUT_BUFA) (SLit FMT_d) (SLit 0) (STDOUT_BUFA) (FMT_d) 0
HS1 ltac:(rewrite HBcode; reflexivity) eq_refl Usp0 G3_0 G4_0 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
eq_refl ltac:(reflexivity) eq_refl ltac:(reflexivity) eq_refl ltac:(reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(lia)
ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(GEO)
ltac:(left; unfold kLowMemEnd; GEO)
ltac:(first [left; unfold kLowMemEnd; GEO | eapply (vf_stack_amem B); [exact (proj1 VO1) | exact Hstk | exact HtopS | GEO | GEO]])
(vo_rest_disj E0 sp0 ap o_rest1 (STDOUT_BUFA) 0 ltac:(vm_compute; reflexivity) G12_0 Hap1 Hsp44 ltac:(GEO) ltac:(GEO) ltac:(lia))
(vo_rest_ok E0 sp0 ap o_rest1 ltac:(vm_compute; reflexivity) G12_0 Hap1 Hap2)
(vo_rest_w E0 o_rest1 ltac:(vm_compute; reflexivity))
(proj1 VO1) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VO1)))
ltac:(intros a Ha; lia) SRA1' SHU1'
ltac:(intros a Ha; lia) ltac:(intros y Hy; lia) ltac:(intros H0; lia)) HAI1).
intros W1' c1' _ HAI1' (-> & ms1' & mat1' & -> & HS1' & HAR1' & HP1' & Heff1' & Hfr1' & Hpm1'). cbn [cfg_model] in HAI1'.
rewrite wvb_wvb in HAI1', HAR1' |- *.
change (vf_after_icpt 34 o_st1 RA_FX OSP_FX 0 []) with o_af1 in HS1'.
assert (VO1' : VO B ly S W sp0 mem md MUT (ms_mem ms1') (with_vm_backing (m_vm_lazy md) mat1' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms1) _ (ms_mem ms1') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ ((STDOUT_BUFA) <= a < (STDOUT_BUFA) + 0))).
- exact VO1.
- exact HAR1'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat1' mat1 md). apply with_vm_backing_same.
- intros a [Ha|Ha]; [left; unfold vf_band, OSP_FX in *; lia | right; unfold MUT, vo_mut; GEO].
- intros a Hr Hna. apply Hfr1'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm1'. }
remember (havoc E0 34 (map (getr (ms_regs ms1')) CLOB)) as E1 eqn:HE1.
assert (OLD1 : forall j, (j < 34)%nat -> ew E1 j = ew E0 j) by (intros j Hj; rewrite HE1; apply ew_havoc_old; exact Hj).
assert (Usp1 : bv_unsigned (ew E1 2) = sp0) by (rewrite OLD1 by (cbv; lia); exact Usp0).
assert (G3_1 : ew E1 3 = w64 (as_gp B)) by (rewrite OLD1 by (cbv; lia); exact G3_0).
assert (G4_1 : ew E1 4 = w64 (as_tp B)) by (rewrite OLD1 by (cbv; lia); exact G4_0).
assert (G12_1 : bv_unsigned (ew E1 12) = ap) by (rewrite OLD1 by (cbv; lia); exact G12_0).
assert (HAE1 : env_agree 32 EA E1)
by (rewrite HE1; apply env_agree_havoc_ge; [cbv; lia | exact HAE0]).
clear HE1 HS1 VO1 SRA1' SHU1' Heff1'.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E1 o_af1 o_st2 _ _ _ HS1' o_run2) HAI1').
intros W2 c2 _ HAI2 (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). cbn [cfg_model] in HAI2. clear HS1'.
rewrite ?wvb_wvb in HAI2 |- *.
assert (VO2 : VO B ly S W sp0 mem md MUT (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms2) mat2 VO1') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF2. intros Hin. destruct (vo_windows_sound E1 o_af1 sp0 _ ltac:(vm_compute; reflexivity) Usp1 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr2. intros Hin. destruct (vo_windows_sound E1 o_af1 sp0 _ ltac:(vm_compute; reflexivity) Usp1 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E1 o_st2 ms2 sp0 HS2 ltac:(vm_compute; reflexivity) Usp1 ltac:(lia)). }
clear VO1' HF2 HFr2.
assert (SRA2' : range_addressable (aview tfibsegs (w_H W) (ms_mem ms2)) SHADOW_OFF 68444 0) by (intros y Hy; lia).
assert (SHU2' : 0 < 0 -> shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms2)) 68444 0) by (intros H0; lia).
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy_ext B LAWS AMEMCPY W E1 o_st2 ms2 _ ly S sp0 o_r02 o_rest2 50 RA_FX OSP_FX
(SLit STDOUT_BUFA) (SLit 68444) (SLit 0) (STDOUT_BUFA) (68444) 0
HS2 ltac:(rewrite HBcode; reflexivity) eq_refl Usp1 G3_1 G4_1 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
eq_refl ltac:(reflexivity) eq_refl ltac:(reflexivity) eq_refl ltac:(reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(lia)
ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(GEO)
ltac:(left; unfold kLowMemEnd; GEO)
ltac:(first [left; unfold kLowMemEnd; GEO | eapply (vf_stack_amem B); [exact (proj1 VO2) | exact Hstk | exact HtopS | GEO | GEO]])
(vo_rest_disj E1 sp0 ap o_rest2 (STDOUT_BUFA) 0 ltac:(vm_compute; reflexivity) G12_1 Hap1 Hsp44 ltac:(GEO) ltac:(GEO) ltac:(lia))
(vo_rest_ok E1 sp0 ap o_rest2 ltac:(vm_compute; reflexivity) G12_1 Hap1 Hap2)
(vo_rest_w E1 o_rest2 ltac:(vm_compute; reflexivity))
(proj1 VO2) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VO2)))
ltac:(intros a Ha; lia) SRA2' SHU2'
ltac:(intros a Ha; lia) ltac:(intros y Hy; lia) ltac:(intros H0; lia)) HAI2).
intros W2' c2' _ HAI2' (-> & ms2' & mat2' & -> & HS2' & HAR2' & HP2' & Heff2' & Hfr2' & Hpm2'). cbn [cfg_model] in HAI2'.
rewrite wvb_wvb in HAI2', HAR2' |- *.
change (vf_after_icpt 50 o_st2 RA_FX OSP_FX 0 []) with o_af2 in HS2'.
assert (VO2' : VO B ly S W sp0 mem md MUT (ms_mem ms2') (with_vm_backing (m_vm_lazy md) mat2' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms2) _ (ms_mem ms2') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ ((STDOUT_BUFA) <= a < (STDOUT_BUFA) + 0))).
- exact VO2.
- exact HAR2'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat2' mat2 md). apply with_vm_backing_same.
- intros a [Ha|Ha]; [left; unfold vf_band, OSP_FX in *; lia | right; unfold MUT, vo_mut; GEO].
- intros a Hr Hna. apply Hfr2'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm2'. }
remember (havoc E1 50 (map (getr (ms_regs ms2')) CLOB)) as E2 eqn:HE2.
assert (OLD2 : forall j, (j < 50)%nat -> ew E2 j = ew E1 j) by (intros j Hj; rewrite HE2; apply ew_havoc_old; exact Hj).
assert (Usp2 : bv_unsigned (ew E2 2) = sp0) by (rewrite OLD2 by (cbv; lia); exact Usp1).
assert (G3_2 : ew E2 3 = w64 (as_gp B)) by (rewrite OLD2 by (cbv; lia); exact G3_1).
assert (G4_2 : ew E2 4 = w64 (as_tp B)) by (rewrite OLD2 by (cbv; lia); exact G4_1).
assert (G12_2 : bv_unsigned (ew E2 12) = ap) by (rewrite OLD2 by (cbv; lia); exact G12_1).
assert (HAE2 : env_agree 32 EA E2)
by (rewrite HE2; apply env_agree_havoc_ge; [cbv; lia | exact HAE1]).
clear HE2 HS2 VO2 SRA2' SHU2' Heff2'.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E2 o_af2 o_st3 _ _ _ HS2' o_run3) HAI2').
intros W3 c3 _ HAI3 (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). cbn [cfg_model] in HAI3. clear HS2'.
rewrite ?wvb_wvb in HAI3 |- *.
assert (VO3 : VO B ly S W sp0 mem md MUT (ms_mem ms3) (with_vm_backing (m_vm_lazy md) mat3 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms3) mat3 VO2') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF3. intros Hin. destruct (vo_windows_sound E2 o_af2 sp0 _ ltac:(vm_compute; reflexivity) Usp2 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr3. intros Hin. destruct (vo_windows_sound E2 o_af2 sp0 _ ltac:(vm_compute; reflexivity) Usp2 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E2 o_st3 ms3 sp0 HS3 ltac:(vm_compute; reflexivity) Usp2 ltac:(lia)). }
clear VO2' HF3 HFr3.
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memset B LAWS AMEMSET W E2 o_st3 ms3 _ ly S sp0 o_r03 o_rest3 66 RA_PAD OSP_PC PAD_OFF 48 1%nat
HS3 ltac:(rewrite HBcode; reflexivity) eq_refl Usp2 G3_2 G4_2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(lia) ltac:(reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_PC; lia) ltac:(unfold OSP_PC, PAD_OFF; lia) ltac:(unfold PAD_OFF; cbn; lia) ltac:(unfold RA_PAD; lia) ltac:(reflexivity)
(vo_rest_ok E2 sp0 ap o_rest3 ltac:(vm_compute; reflexivity) G12_2 Hap1 Hap2)
(vo_rest_w E2 o_rest3 ltac:(vm_compute; reflexivity))
(proj1 VO3) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VO3)))) HAI3).
intros W3' c3' _ HAI3' (-> & ms3' & mat3' & -> & HS3' & HAR3' & HP3' & Hfr3' & Hpm3'). cbn [cfg_model] in HAI3'.
rewrite wvb_wvb in HAI3', HAR3' |- *.
change (vf_after_icpt 66 o_st3 RA_PAD OSP_PC PAD_OFF (repeat 48 1%nat)) with o_af3 in HS3'.
assert (VO3' : VO B ly S W sp0 mem md MUT (ms_mem ms3') (with_vm_backing (m_vm_lazy md) mat3' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms3) _ (ms_mem ms3') _
(fun a => (sp0 + OSP_PC - ESTACK <= a < sp0 + OSP_PC) \/ (sp0 + PAD_OFF <= a < sp0 + PAD_OFF + 1))).
- exact VO3.
- exact HAR3'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat3' mat3 md). apply with_vm_backing_same.
- intros a Ha. left. unfold vf_band, OSP_PC, PAD_OFF in *. lia.
- intros a Hr Hna. apply Hfr3'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; cbn; exact H'].
- exact Hpm3'. }
remember (havoc E2 66 (map (getr (ms_regs ms3')) CLOB)) as E3 eqn:HE3.
assert (OLD3 : forall j, (j < 66)%nat -> ew E3 j = ew E2 j) by (intros j Hj; rewrite HE3; apply ew_havoc_old; exact Hj).
assert (Usp3 : bv_unsigned (ew E3 2) = sp0) by (rewrite OLD3 by (cbv; lia); exact Usp2).
assert (G3_3 : ew E3 3 = w64 (as_gp B)) by (rewrite OLD3 by (cbv; lia); exact G3_2).
assert (G4_3 : ew E3 4 = w64 (as_tp B)) by (rewrite OLD3 by (cbv; lia); exact G4_2).
assert (G12_3 : bv_unsigned (ew E3 12) = ap) by (rewrite OLD3 by (cbv; lia); exact G12_2).
assert (HAE3 : env_agree 32 EA E3)
by (rewrite HE3; apply env_agree_havoc_ge; [cbv; lia | exact HAE2]).
clear HE3 HS3 VO3.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E3 o_af3 o_st4 _ _ _ HS3' o_run4) HAI3').
intros W4 c4 _ HAI4 (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). cbn [cfg_model] in HAI4. clear HS3'.
rewrite ?wvb_wvb in HAI4 |- *.
assert (VO4 : VO B ly S W sp0 mem md MUT (ms_mem ms4) (with_vm_backing (m_vm_lazy md) mat4 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms4) mat4 VO3') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF4. intros Hin. destruct (vo_windows_sound E3 o_af3 sp0 _ ltac:(vm_compute; reflexivity) Usp3 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr4. intros Hin. destruct (vo_windows_sound E3 o_af3 sp0 _ ltac:(vm_compute; reflexivity) Usp3 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E3 o_st4 ms4 sp0 HS4 ltac:(vm_compute; reflexivity) Usp3 ltac:(lia)). }
clear VO3' HF4 HFr4.
pose proof HS4 as HSc4. destruct HSc4 as (_ & _ & _ & _ & _ & _ & _ & Hmem4 & _). cbn [restrict ms_mem] in Hmem4.
assert (PAD4 : aview tfibsegs (w_H W) (ms_mem ms4) (sp0 + PAD_OFF) = Some 48).
{ replace (sp0 + PAD_OFF) with (sp0 + PAD_OFF + Z.of_nat 0) by lia.
apply (lit_buf_aview W E3 (ms_mem ms4) (ss_mem o_st4) (SOff 2 PAD_OFF) (sp0 + PAD_OFF) 1 [48] Hmem4 ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot]; rewrite Usp3; reflexivity) ltac:(repeat constructor; lia) 0%nat ltac:(lia)). }
clear Hmem4.
destruct (vf_stack_shadow B LAWS W ly S (ms_mem ms4) _ sp0 (sp0 + PAD_OFF) 1 (proj1 VO4) Hstk Htop ltac:(unfold PAD_OFF; lia) ltac:(unfold PAD_OFF; lia) ltac:(lia)) as [SRA4' SHU4'].
destruct (vo_shadow_xfer B ly S W sp0 mem md STDOUT_BUFA (STDOUT_BUFA + 1) (ms_mem ms4) _ STDOUT_BUFA STDOUT_BSZ STDOUT_BUFA 1 VO4 ltac:(unfold STDOUT_BSZ; lia) Hstk Hra_b Hhull_b
ltac:(unfold STDOUT_BUFA; lia) ltac:(lia) ltac:(unfold STDOUT_BSZ; lia) ltac:(rewrite KHI; unfold STDOUT_BUFA, STDOUT_BSZ; lia)) as [DRA4' DHU4'].
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy_ext B LAWS AMEMCPY W E3 o_st4 ms4 _ ly S sp0 o_r04 o_rest4 82 RA_FX OSP_FX
(SLit STDOUT_BUFA) (SOff 2 PAD_OFF) (SLit 1) (STDOUT_BUFA) (sp0 + PAD_OFF) 1
HS4 ltac:(rewrite HBcode; reflexivity) eq_refl Usp3 G3_3 G4_3 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
eq_refl ltac:(reflexivity) eq_refl ltac:(cbn [sv_denot]; rewrite Usp3; reflexivity) eq_refl ltac:(reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(lia)
ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(GEO)
ltac:(left; unfold kLowMemEnd; GEO)
ltac:(first [left; unfold kLowMemEnd; GEO | eapply (vf_stack_amem B); [exact (proj1 VO4) | exact Hstk | exact HtopS | GEO | GEO]])
(vo_rest_disj E3 sp0 ap o_rest4 (STDOUT_BUFA) 1 ltac:(vm_compute; reflexivity) G12_3 Hap1 Hsp44 ltac:(GEO) ltac:(GEO) ltac:(lia))
(vo_rest_ok E3 sp0 ap o_rest4 ltac:(vm_compute; reflexivity) G12_3 Hap1 Hap2)
(vo_rest_w E3 o_rest4 ltac:(vm_compute; reflexivity))
(proj1 VO4) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VO4)))
ltac:(intros a Ha; replace a with (sp0 + PAD_OFF) by lia; rewrite PAD4; discriminate) SRA4' SHU4'
ltac:(intros a Ha; split; [apply stdout_buf_writable; unfold STDOUT_BSZ; lia | apply HBown; right; unfold STDOUT_BSZ; lia]) ltac:(exact DRA4') ltac:(exact DHU4')) HAI4).
intros W4' c4' _ HAI4' (-> & ms4' & mat4' & -> & HS4' & HAR4' & HP4' & Heff4' & Hfr4' & Hpm4'). cbn [cfg_model] in HAI4'.
rewrite wvb_wvb in HAI4', HAR4' |- *.
change (vf_after_icpt 82 o_st4 RA_FX OSP_FX 0 []) with o_af4 in HS4'.
assert (VO4' : VO B ly S W sp0 mem md MUT (ms_mem ms4') (with_vm_backing (m_vm_lazy md) mat4' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms4) _ (ms_mem ms4') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ ((STDOUT_BUFA) <= a < (STDOUT_BUFA) + 1))).
- exact VO4.
- exact HAR4'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat4' mat4 md). apply with_vm_backing_same.
- intros a [Ha|Ha]; [left; unfold vf_band, OSP_FX in *; lia | right; unfold MUT, vo_mut; GEO].
- intros a Hr Hna. apply Hfr4'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm4'. }
assert (BUF04' : aview tfibsegs (w_H W) (ms_mem ms4') (STDOUT_BUFA) = Some 48).
{ rewrite <- PAD4, <- (Z.add_0_r STDOUT_BUFA), <- (Z.add_0_r (sp0 + PAD_OFF)). apply (Heff4' 0). lia. }
remember (havoc E3 82 (map (getr (ms_regs ms4')) CLOB)) as E4 eqn:HE4.
assert (OLD4 : forall j, (j < 82)%nat -> ew E4 j = ew E3 j) by (intros j Hj; rewrite HE4; apply ew_havoc_old; exact Hj).
assert (Usp4 : bv_unsigned (ew E4 2) = sp0) by (rewrite OLD4 by (cbv; lia); exact Usp3).
assert (G3_4 : ew E4 3 = w64 (as_gp B)) by (rewrite OLD4 by (cbv; lia); exact G3_3).
assert (G4_4 : ew E4 4 = w64 (as_tp B)) by (rewrite OLD4 by (cbv; lia); exact G4_3).
assert (G12_4 : bv_unsigned (ew E4 12) = ap) by (rewrite OLD4 by (cbv; lia); exact G12_3).
assert (HAE4 : env_agree 32 EA E4)
by (rewrite HE4; apply env_agree_havoc_ge; [cbv; lia | exact HAE3]).
clear HE4 HS4 VO4 SRA4' SHU4' Heff4'.
clear PAD4 DRA4' DHU4'.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E4 o_af4 o_st5 _ _ _ HS4' o_run5) HAI4').
intros W5 c5 _ HAI5 (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). cbn [cfg_model] in HAI5. clear HS4'.
rewrite ?wvb_wvb in HAI5 |- *.
assert (VO5 : VO B ly S W sp0 mem md MUT (ms_mem ms5) (with_vm_backing (m_vm_lazy md) mat5 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms5) mat5 VO4') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF5. intros Hin. destruct (vo_windows_sound E4 o_af4 sp0 _ ltac:(vm_compute; reflexivity) Usp4 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr5. intros Hin. destruct (vo_windows_sound E4 o_af4 sp0 _ ltac:(vm_compute; reflexivity) Usp4 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E4 o_st5 ms5 sp0 HS5 ltac:(vm_compute; reflexivity) Usp4 ltac:(lia)). }
assert (BUF05 : aview tfibsegs (w_H W) (ms_mem ms5) (STDOUT_BUFA) = Some 48).
{ rewrite <- BUF04'. apply aview_eq_of. apply HFr5. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (vo_windows_sound E4 o_af4 sp0 _ ltac:(vm_compute; reflexivity) Usp4 Hin) as [Hw|Hw]; [unfold vf_band in Hw; GEO | unfold vo_file, F_STDOUT, FILE_SZ in Hw; GEO]. }
clear VO4' HF5 HFr5 BUF04'.
assert (SRA5' : range_addressable (aview tfibsegs (w_H W) (ms_mem ms5)) SHADOW_OFF (sp0 + PAD_OFF) 0) by (intros y Hy; lia).
assert (SHU5' : 0 < 0 -> shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms5)) (sp0 + PAD_OFF) 0) by (intros H0; lia).
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy_ext B LAWS AMEMCPY W E4 o_st5 ms5 _ ly S sp0 o_r05 o_rest5 98 RA_FX OSP_FX
(SLit (STDOUT_BUFA + 1)) (SOff 2 PAD_OFF) (SLit 0) (STDOUT_BUFA + 1) (sp0 + PAD_OFF) 0
HS5 ltac:(rewrite HBcode; reflexivity) eq_refl Usp4 G3_4 G4_4 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
eq_refl ltac:(reflexivity) eq_refl ltac:(cbn [sv_denot]; rewrite Usp4; reflexivity) eq_refl ltac:(reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(lia)
ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(GEO)
ltac:(left; unfold kLowMemEnd; GEO)
ltac:(first [left; unfold kLowMemEnd; GEO | eapply (vf_stack_amem B); [exact (proj1 VO5) | exact Hstk | exact HtopS | GEO | GEO]])
(vo_rest_disj E4 sp0 ap o_rest5 (STDOUT_BUFA + 1) 0 ltac:(vm_compute; reflexivity) G12_4 Hap1 Hsp44 ltac:(GEO) ltac:(GEO) ltac:(lia))
(vo_rest_ok E4 sp0 ap o_rest5 ltac:(vm_compute; reflexivity) G12_4 Hap1 Hap2)
(vo_rest_w E4 o_rest5 ltac:(vm_compute; reflexivity))
(proj1 VO5) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VO5)))
ltac:(intros a Ha; lia) SRA5' SHU5'
ltac:(intros a Ha; lia) ltac:(intros y Hy; lia) ltac:(intros H0; lia)) HAI5).
intros W5' c5' _ HAI5' (-> & ms5' & mat5' & -> & HS5' & HAR5' & HP5' & Heff5' & Hfr5' & Hpm5'). cbn [cfg_model] in HAI5'.
rewrite wvb_wvb in HAI5', HAR5' |- *.
change (vf_after_icpt 98 o_st5 RA_FX OSP_FX 0 []) with o_af5 in HS5'.
assert (VO5' : VO B ly S W sp0 mem md MUT (ms_mem ms5') (with_vm_backing (m_vm_lazy md) mat5' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms5) _ (ms_mem ms5') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ ((STDOUT_BUFA + 1) <= a < (STDOUT_BUFA + 1) + 0))).
- exact VO5.
- exact HAR5'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat5' mat5 md). apply with_vm_backing_same.
- intros a [Ha|Ha]; [left; unfold vf_band, OSP_FX in *; lia | right; unfold MUT, vo_mut; GEO].
- intros a Hr Hna. apply Hfr5'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm5'. }
assert (BUF05' : aview tfibsegs (w_H W) (ms_mem ms5') (STDOUT_BUFA) = Some 48).
{ rewrite <- BUF05. apply Hfr5'; [GEO | GEO | GEO]. }
remember (havoc E4 98 (map (getr (ms_regs ms5')) CLOB)) as E5 eqn:HE5.
assert (OLD5 : forall j, (j < 98)%nat -> ew E5 j = ew E4 j) by (intros j Hj; rewrite HE5; apply ew_havoc_old; exact Hj).
assert (Usp5 : bv_unsigned (ew E5 2) = sp0) by (rewrite OLD5 by (cbv; lia); exact Usp4).
assert (G3_5 : ew E5 3 = w64 (as_gp B)) by (rewrite OLD5 by (cbv; lia); exact G3_4).
assert (G4_5 : ew E5 4 = w64 (as_tp B)) by (rewrite OLD5 by (cbv; lia); exact G4_4).
assert (G12_5 : bv_unsigned (ew E5 12) = ap) by (rewrite OLD5 by (cbv; lia); exact G12_4).
assert (HAE5 : env_agree 32 EA E5)
by (rewrite HE5; apply env_agree_havoc_ge; [cbv; lia | exact HAE4]).
clear HE5 HS5 VO5 SRA5' SHU5' Heff5' BUF05.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E5 o_af5 o_st6 _ _ _ HS5' o_run6) HAI5').
intros W6 c6 _ HAI6 (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). cbn [cfg_model] in HAI6. clear HS5'.
rewrite ?wvb_wvb in HAI6 |- *.
assert (VO6 : VO B ly S W sp0 mem md MUT (ms_mem ms6) (with_vm_backing (m_vm_lazy md) mat6 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms6) mat6 VO5') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF6. intros Hin. destruct (vo_windows_sound E5 o_af5 sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr6. intros Hin. destruct (vo_windows_sound E5 o_af5 sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present_ecall W E5 o_st6 ms6 sp0 HS6 ltac:(vm_compute; reflexivity) Usp5 ltac:(lia)). }
assert (BUF06 : aview tfibsegs (w_H W) (ms_mem ms6) (STDOUT_BUFA) = Some 48).
{ rewrite <- BUF05'. apply aview_eq_of. apply HFr6. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (vo_windows_sound E5 o_af5 sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin) as [Hw|Hw]; [unfold vf_band in Hw; GEO | unfold vo_file, F_STDOUT, FILE_SZ in Hw; GEO]. }
clear VO5' HF6 HFr6 BUF05'.
eapply (srz_sym_ioctl_enotty W E5 o_st6 ms6 _ (Z_to_bv 64 1) ch _ HAI6 HS6 eq_refl ltac:(vm_compute; reflexivity) eq_refl
ltac:(eapply fdchan_sbm; [exact Hch | apply with_vm_backing_same]) eq_refl ltac:(vm_compute; reflexivity)).
intros ms6r HS6r Hmm6r.
change (resume o_st6 (SLit (2 ^ 64 - 25)) (ss_mem o_st6) (ss_facts o_st6)) with o_af6 in HS6r.
assert (VO6r : VO B ly S W sp0 mem md MUT (ms_mem ms6r) (with_vm_backing (m_vm_lazy md) mat6 md)) by (rewrite Hmm6r; exact VO6).
assert (BUF06r : aview tfibsegs (w_H W) (ms_mem ms6r) (STDOUT_BUFA) = Some 48) by (rewrite Hmm6r; exact BUF06).
clear HS6 VO6 BUF06.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E5 o_af6 o_st7 _ _ _ HS6r o_run7) HAI6).
intros W7 c7 _ HAI7 (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). cbn [cfg_model] in HAI7. clear HS6r.
rewrite ?wvb_wvb in HAI7 |- *.
assert (VO7 : VO B ly S W sp0 mem md MUT (ms_mem ms7) (with_vm_backing (m_vm_lazy md) mat7 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms7) mat7 VO6r) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF7. intros Hin. destruct (vo_windows_sound E5 o_af6 sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr7. intros Hin. destruct (vo_windows_sound E5 o_af6 sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present_ecall W E5 o_st7 ms7 sp0 HS7 ltac:(vm_compute; reflexivity) Usp5 ltac:(lia)). }
assert (BUF07 : aview tfibsegs (w_H W) (ms_mem ms7) (STDOUT_BUFA) = Some 48).
{ rewrite <- BUF06r. apply aview_eq_of. apply HFr7. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (vo_windows_sound E5 o_af6 sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin) as [Hw|Hw]; [unfold vf_band in Hw; GEO | unfold vo_file, F_STDOUT, FILE_SZ in Hw; GEO]. }
clear VO6r HF7 HFr7 BUF06r.
pose proof HS7 as HSc7. destruct HSc7 as (_ & _ & _ & _ & _ & _ & Hregs7 & Hmem7 & HG7). cbn [restrict ms_mem] in Hmem7.
pose proof (lit_buf_sound tfibsegs E5 (mrestrict (w_H W) (ms_mem ms7)) (ss_mem o_st7) (SLit (F_STDOUT + 120)) 4 [1; 0; 0; 0] Hmem7
ltac:(vm_compute; reflexivity)) as Hfdrd. cbn [sv_denot] in Hfdrd.
pose proof (lit_buf_sound tfibsegs E5 (mrestrict (w_H W) (ms_mem ms7)) (ss_mem o_st7) (SLit 83948) 1 [10] Hmem7
ltac:(vm_compute; reflexivity)) as Hnlrd.
change (map (Z_to_bv 8) [48; 10]) with ([Z_to_bv 8 48] ++ map (Z_to_bv 8) [10]).
eapply (srz_sym_stdio_writev2 W E5 o_st7 ms7 _ (Z_to_bv 64 1) ch 0 2 (-1120) F_STDOUT _ (SLit STDOUT_BUFA) (SLit 1) (SLit 83948) (SLit 1)
([Z_to_bv 8 48]) (map (Z_to_bv 8) [10]) (map (Z_to_bv 8) [1; 0; 0; 0]) 114 T HAI7 HS7 eq_refl eq_refl eq_refl).
- reflexivity.
- eapply fdchan_sbm; [exact Hch | apply with_vm_backing_same].
- reflexivity.
- vm_compute. reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- match goal with |- U _ ?x = _ => let x' := eval vm_compute in x in change x with x' end. rewrite !U_SLit. reflexivity.
- match goal with |- U _ ?x = _ => let x' := eval vm_compute in x in change x with x' end. rewrite U_SLit. reflexivity.
- reflexivity.
- reflexivity.
- cbn. lia. - cbn. lia. - cbn. lia. - cbn. lia.
- vm_compute. reflexivity.
-   cbn [sv_denot]. change (word_to_nat (Z_to_bv 64 1)) with 1%nat.
apply (proj2 (rdn_mbytes tfibsegs _ 1%nat STDOUT_BUFA [Z_to_bv 8 48])). split; [reflexivity|].
intros i Hi. replace i with 0%nat by lia. rewrite Z.add_0_r. destruct (aview_mbyte _ _ _ _ BUF07) as (b & Hb & Hbv).
rewrite Hb. cbn. f_equal. apply bv_eq. rewrite Hbv. reflexivity.
-   change (word_to_nat (sv_denot E5 (SLit 1))) with 1%nat. exact Hnlrd.
- rewrite !U_SLit. change (zcanon 1) with 1. lia.
- rewrite !U_SLit. change (zcanon STDOUT_BUFA) with STDOUT_BUFA. change (zcanon 1) with 1. unfold STDOUT_BUFA. lia.
- rewrite !U_SLit, Usp5. change (zcanon STDOUT_BUFA) with STDOUT_BUFA. change (zcanon 1) with 1. unfold STDOUT_BUFA. lia.
- rewrite !U_SLit. change (zcanon 83948) with 83948. change (zcanon 1) with 1. lia.
- rewrite !U_SLit, Usp5. change (zcanon 83948) with 83948. change (zcanon 1) with 1. lia.
- exact Hfdrd.
- vm_compute. reflexivity.
- unfold F_STDOUT. lia.
- unfold F_STDOUT. lia.
- rewrite Usp5. unfold F_STDOUT. lia.
- rewrite Usp5. lia.
- rewrite Usp5. lia.
- vm_compute. reflexivity.
-
intros ms7' ws7 mat7' HS7' HF7' HFr7' HAI7'. rewrite ?wvb_wvb in HAI7' |- *.
change (wl_after o_st7 0 (-1120) 114) with o_af7 in HS7'.
remember (havoc E5 114 ws7) as E6 eqn:HE6.
assert (OLD6 : forall j, (j < 114)%nat -> ew E6 j = ew E5 j) by (intros j Hj; rewrite HE6; apply ew_havoc_old; exact Hj).
assert (Usp6 : bv_unsigned (ew E6 2) = sp0) by (rewrite OLD6 by (cbv; lia); exact Usp5).
assert (G3_6 : ew E6 3 = w64 (as_gp B)) by (rewrite OLD6 by (cbv; lia); exact G3_5).
assert (G4_6 : ew E6 4 = w64 (as_tp B)) by (rewrite OLD6 by (cbv; lia); exact G4_5).
assert (G12_6 : bv_unsigned (ew E6 12) = ap) by (rewrite OLD6 by (cbv; lia); exact G12_5).
assert (HAE6 : env_agree 32 EA E6)
by (rewrite HE6; apply env_agree_havoc_ge; [cbv; lia | exact HAE5]).
assert (VO7' : VO B ly S W sp0 mem md MUT (ms_mem ms7') (with_vm_backing (m_vm_lazy md) mat7' md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms7') mat7' VO7) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF7'. intros Hin. destruct (vo_windows_sound E5 o_st7 sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr7'. intros Hin. destruct (vo_windows_sound E5 o_st7 sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E6 o_af7 ms7' sp0 HS7' ltac:(vm_compute; reflexivity) Usp6 ltac:(lia)). }
clear HE6 HS7 VO7 Hfdrd Hnlrd Hregs7 Hmem7 HG7 HF7' HFr7' BUF07.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E6 o_af7 o_st8 _ _ _ HS7' o_run8) HAI7').
intros W8 c8 _ HAI8 (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). cbn [cfg_model] in HAI8. clear HS7'.
rewrite ?wvb_wvb in HAI8 |- *.
assert (VO8 : VO B ly S W sp0 mem md MUT (ms_mem ms8) (with_vm_backing (m_vm_lazy md) mat8 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms8) mat8 VO7') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF8. intros Hin. destruct (vo_windows_sound E6 o_af7 sp0 _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr8. intros Hin. destruct (vo_windows_sound E6 o_af7 sp0 _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E6 o_st8 ms8 sp0 HS8 ltac:(vm_compute; reflexivity) Usp6 ltac:(lia)). }
clear VO7' HF8 HFr8.
assert (SRA8' : range_addressable (aview tfibsegs (w_H W) (ms_mem ms8)) SHADOW_OFF 83949 0) by (intros y Hy; lia).
assert (SHU8' : 0 < 0 -> shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms8)) 83949 0) by (intros H0; lia).
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy_ext B LAWS AMEMCPY W E6 o_st8 ms8 _ ly S sp0 o_r08 o_rest8 125 RA_FX OSP_FX
(SLit STDOUT_BUFA) (SLit 83949) (SLit 0) (STDOUT_BUFA) (83949) 0
HS8 ltac:(rewrite HBcode; reflexivity) eq_refl Usp6 G3_6 G4_6 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
eq_refl ltac:(reflexivity) eq_refl ltac:(reflexivity) eq_refl ltac:(reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(lia)
ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(GEO)
ltac:(left; unfold kLowMemEnd; GEO)
ltac:(first [left; unfold kLowMemEnd; GEO | eapply (vf_stack_amem B); [exact (proj1 VO8) | exact Hstk | exact HtopS | GEO | GEO]])
(vo_rest_disj E6 sp0 ap o_rest8 (STDOUT_BUFA) 0 ltac:(vm_compute; reflexivity) G12_6 Hap1 Hsp44 ltac:(GEO) ltac:(GEO) ltac:(lia))
(vo_rest_ok E6 sp0 ap o_rest8 ltac:(vm_compute; reflexivity) G12_6 Hap1 Hap2)
(vo_rest_w E6 o_rest8 ltac:(vm_compute; reflexivity))
(proj1 VO8) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VO8)))
ltac:(intros a Ha; lia) SRA8' SHU8'
ltac:(intros a Ha; lia) ltac:(intros y Hy; lia) ltac:(intros H0; lia)) HAI8).
intros W8' c8' _ HAI8' (-> & ms8' & mat8' & -> & HS8' & HAR8' & HP8' & Heff8' & Hfr8' & Hpm8'). cbn [cfg_model] in HAI8'.
rewrite wvb_wvb in HAI8', HAR8' |- *.
change (vf_after_icpt 125 o_st8 RA_FX OSP_FX 0 []) with o_af8 in HS8'.
assert (VO8' : VO B ly S W sp0 mem md MUT (ms_mem ms8') (with_vm_backing (m_vm_lazy md) mat8' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms8) _ (ms_mem ms8') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ ((STDOUT_BUFA) <= a < (STDOUT_BUFA) + 0))).
- exact VO8.
- exact HAR8'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat8' mat8 md). apply with_vm_backing_same.
- intros a [Ha|Ha]; [left; unfold vf_band, OSP_FX in *; lia | right; unfold MUT, vo_mut; GEO].
- intros a Hr Hna. apply Hfr8'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm8'. }
remember (havoc E6 125 (map (getr (ms_regs ms8')) CLOB)) as E7 eqn:HE7.
assert (OLD7 : forall j, (j < 125)%nat -> ew E7 j = ew E6 j) by (intros j Hj; rewrite HE7; apply ew_havoc_old; exact Hj).
assert (Usp7 : bv_unsigned (ew E7 2) = sp0) by (rewrite OLD7 by (cbv; lia); exact Usp6).
assert (G3_7 : ew E7 3 = w64 (as_gp B)) by (rewrite OLD7 by (cbv; lia); exact G3_6).
assert (G4_7 : ew E7 4 = w64 (as_tp B)) by (rewrite OLD7 by (cbv; lia); exact G4_6).
assert (G12_7 : bv_unsigned (ew E7 12) = ap) by (rewrite OLD7 by (cbv; lia); exact G12_6).
assert (HAE7 : env_agree 32 EA E7)
by (rewrite HE7; apply env_agree_havoc_ge; [cbv; lia | exact HAE6]).
clear HE7 HS8 VO8 SRA8' SHU8' Heff8'.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E7 o_af8 o_st9 _ _ _ HS8' o_run9) HAI8').
intros W9 c9 _ HAI9 (-> & ms9 & mat9 & -> & HS9 & HF9 & HFr9). cbn [cfg_model] in HAI9. clear HS8'.
rewrite ?wvb_wvb in HAI9 |- *.
assert (VO9 : VO B ly S W sp0 mem md MUT (ms_mem ms9) (with_vm_backing (m_vm_lazy md) mat9 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms9) mat9 VO8') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF9. intros Hin. destruct (vo_windows_sound E7 o_af8 sp0 _ ltac:(vm_compute; reflexivity) Usp7 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr9. intros Hin. destruct (vo_windows_sound E7 o_af8 sp0 _ ltac:(vm_compute; reflexivity) Usp7 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E7 o_st9 ms9 sp0 HS9 ltac:(vm_compute; reflexivity) Usp7 ltac:(lia)). }
clear VO8' HF9 HFr9.
eapply (SRr_srealizes tfibsegs W _
(fun W' c' => W' = W /\ exists mat', c' = mkCfg (mkst (ms_regs ms9) (v_jalr (getr (ms_regs ms9) 1) 0) (ms_mem ms9) (seg_rom tfibsegs))
(with_vm_backing (m_vm_lazy md) mat' md)) T); [ | exact HAI9 | ].
{ eapply (SRr_ret_at tfibsegs tfibmusl_tbl tfibmusl_tbl_ok Hwx W E7); [exact HS9 | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb. split; [reflexivity|]. exists mat'. reflexivity. }
intros WR cR _ HAIR (-> & matR & ->). cbn [cfg_model] in HAIR.
destruct VO9 as (HAR9 & Hsbm9 & Hpb9 & Hfr9 & Hpm9).
rreg HS9 (1%bv : bv 5) Q1.
rewrite OLD7, OLD6, OLD5, OLD4, OLD3, OLD2, OLD1 in Q1 by (cbv; lia). rewrite E0_1 in Q1.
pose proof (st_ok_restrict_reg tfibsegs (w_H W) E7 _ _ 10 HS9) as Q10. cbn [ms_regs restrict] in Q10.
match type of Q10 with _ = sv_denot _ ?v => let v' := eval vm_compute in v in change v with v' in Q10 end. cbn [sv_denot] in Q10.
replace (v_jalr (getr (ms_regs ms9) 1) 0) with (w64 (raZ regs))
by (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra).
assert (SBMR : same_but_materialized (with_vm_backing (m_vm_lazy md) mat9 md) (with_vm_backing (m_vm_lazy md) matR md))
by (rewrite <- (wvb_collapse (m_vm_lazy md) matR mat9 md); apply with_vm_backing_same).
pose proof (same_but_materialized_frame _ _ SBMR) as MF.
apply (HK (ms_regs ms9) (ms_mem ms9) (with_vm_backing (m_vm_lazy md) matR md)).
* apply (al_frame _ _ LAWS ly S W (ms_mem ms9) _ (ms_mem ms9) _ HAR9); [intros; reflexivity | intros a Hv; exact Hv | apply MF | apply MF | apply MF | exact (AE2y.hs_kept_refl _ _)].
* exact (aregs_preserved_of_st_ok _ E7 _ _ regs _ HS9 HAE7 ltac:(vm_compute; reflexivity)).
* apply with_vm_backing_same.
* rewrite Q10. reflexivity.
* destruct HS9 as (_ & _ & _ & _ & _ & _ & _ & Hmem9 & _).
split.
-- unfold ofile_is, stdout_fields1.
repeat apply Forall_cons; try apply Forall_nil;
(eapply (val_mem_of_lit E7 (mrestrict (w_H W) (ms_mem ms9)) (ss_mem o_st9) _ _ _ Hmem9); vm_compute; reflexivity).
-- eapply (val_mem_of_lit E7 (mrestrict (w_H W) (ms_mem ms9)) (ss_mem o_st9) _ _ _ Hmem9); vm_compute; reflexivity.
* exact Hfr9.
* exact Hpm9.
* exact HAIR.
Qed.
Theorem tfib_vfprintf_stdout_next : forall ly S (W : world tfibsegs) regs mem md ap cval wp T,
ecall_pre tfibsegs B ly S W regs mem md ->
2 ^ 44 <= spZ regs -> ly_stk_lo ly + VF_STK <= spZ regs ->
(forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) ->
getr regs 10 = w64 F_STDOUT -> getr regs 11 = w64 FMT_d -> getr regs 12 = w64 ap ->
spZ regs <= ap -> ap + 8 <= 2 ^ 47 -> ap mod 8 = 0 ->
val_mem tfibsegs (mrestrict (w_H W) mem) ap 8 0 ->
stdout_mid wp (mrestrict (w_H W) mem) -> STDOUT_BUFA <= wp -> wp + 2 <= STDOUT_BUFA + STDOUT_BSZ ->
(forall a, vo_file a \/ STDOUT_BUFA <= a < STDOUT_BUFA + STDOUT_BSZ -> ~ aowned B ly S a) ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
ro_img (mrestrict (w_H W) mem) ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF STDOUT_BUFA STDOUT_BSZ ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) STDOUT_BUFA STDOUT_BSZ ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF FMT_d 4 ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) FMT_d 4 ->
AI tfibsegs (w_H W) (w_A W) md ->
(forall regs' mem' md',
AR tfibsegs B ly S W mem' md' -> aregs_preserved regs regs' -> same_but_materialized md md' ->
getr regs' 10 = w64 2 ->
stdout_mid (wp + 2) (mrestrict (w_H W) mem') ->
aview tfibsegs (w_H W) mem' wp = Some 48 -> aview tfibsegs (w_H W) mem' (wp + 1) = Some 10 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_band (spZ regs) a -> ~ vo_mut wp (wp + 2) a ->
aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vo_mut wp (wp + 2) a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
AI tfibsegs (w_H W) (w_A W) md' ->
srealizes tfibsegs (cfg_at tfibsegs (raZ regs) regs' mem' md') T) ->
srealizes tfibsegs (cfg_at tfibsegs A_vfprintf regs mem md) T.
Proof.
intros ly S W regs mem md ap cval wp T HPRE Hsp44 Hstk Hpres Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg
HFP Hwp1 Hwp2 HBown Hgot Hcan Hcv Hro Hra_b Hhull_b Hra_f Hhull_f HAI0 HK.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity. assert (HVF : VF_STK = 9104) by reflexivity.
assert (HFF : F_STDOUT = 665192) by reflexivity. assert (HFS : FILE_SZ = 232) by reflexivity.
assert (HBF : STDOUT_BUFA = 6264480) by reflexivity. assert (HBS : STDOUT_BSZ = 1024) by reflexivity.
assert (HFD : FMT_d = 83946) by reflexivity. assert (HPO : PAD_OFF = -736) by reflexivity. assert (HOX : OSP_FX = -976) by reflexivity.
assert (HBE : BUFEND = 6265504) by reflexivity.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by reflexivity.
set (sp0 := spZ regs) in *. assert (HtopS : sp0 < kHighMemEnd) by (rewrite KHI; lia).
assert (Hsp47 : sp0 <= 2 ^ 47) by lia.
set (MUT := vo_mut wp (wp + 2)) in *.
assert (MUTimg : forall a, MUT a -> img_byte_ok tfibsegs a = true) by (intros a Ha; apply (vo_mut_img wp (wp + 2) a); [lia | lia | exact Ha]).
assert (MUTdec : forall a, MUT a \/ ~ MUT a) by (intros a; apply vo_mut_dec).
assert (HFownM : forall a, MUT a -> ~ aowned B ly S a) by (intros a [Ha|Ha]; apply HBown; [left; exact Ha | right; lia]).
unfold cfg_at. change (w64 A_vfprintf) with (Z_to_bv 64 A_vfprintf).
pose proof (vo_entry1 W regs mem ap cval wp Hsp44 Hsp47 Hal16 ltac:(intros a Ha; apply Hpres; exact Ha) Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg
HFP ltac:(lia) Hgot Hcan Hcv Hro) as HS0.
set (EL := [Z_to_bv 64 0; Z_to_bv 64 cval; Z_to_bv 64 wp]) in *.
remember (Ereg regs EL) as E0 eqn:HE0.
assert (EE : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E0 i = getr regs r)
by (intros i r Hi; rewrite HE0; exact (ew_Ereg_nat regs _ i r Hi)).
pose proof (EE 1%nat (1%bv : bv 5) eq_refl) as E0_1.
assert (Usp0 : bv_unsigned (ew E0 2) = sp0) by (rewrite (EE 2%nat (2%bv : bv 5) eq_refl); reflexivity).
assert (G3_0 : ew E0 3 = w64 (as_gp B)) by (rewrite (EE 3%nat (3%bv : bv 5) eq_refl); exact Hgp).
assert (G4_0 : ew E0 4 = w64 (as_tp B)) by (rewrite (EE 4%nat (4%bv : bv 5) eq_refl); exact Htp).
assert (G12_0 : bv_unsigned (ew E0 12) = ap) by (rewrite (EE 12%nat (12%bv : bv 5) eq_refl), Ha2; apply unsigned_lit_small; lia).
assert (A34_0 : bv_unsigned (ew E0 34) = wp) by (rewrite HE0; pose proof (ew_Ereg_extra regs EL 2) as X; cbn [nth Nat.add EL] in X; rewrite X; apply unsigned_lit_small; lia).
assert (HAE0 : env_agree 32 (Ereg regs EL) E0) by (rewrite HE0; split; [intros i Hi; reflexivity | reflexivity]).
set (EA := Ereg regs EL) in *.
clear HE0 EE.
pose proof (VO_init B ly S W sp0 mem md MUT HAR Hpres) as VO0.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E0 ss_vo1 n_st1 _ _ _ HS0 n_run1) HAI0).
intros W1 c1 _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [cfg_model] in HAI1. clear HS0.
rewrite ?wvb_wvb in HAI1 |- *.
assert (VO1 : VO B ly S W sp0 mem md MUT (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms1) mat1 VO0) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF1. intros Hin. destruct (vo_windows_sound E0 ss_vo1 sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr1. intros Hin. destruct (vo_windows_sound E0 ss_vo1 sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E0 n_st1 ms1 sp0 HS1 ltac:(vm_compute; reflexivity) Usp0 ltac:(lia)). }
clear VO0 HF1 HFr1.
pose proof (st_ok_add_cond tfibsegs E0 n_st1 _ BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (0 - BUFEND))) (SLit 0) HS1 ltac:(rewrite branch_geu_U, U_SLit; change (zcanon 0) with 0; apply Bool.negb_true_iff; apply Z.ltb_ge; pose proof (U_range E0 (SAlu ALU_SUB (SLit 0) (SOff 34 (0 - BUFEND)))); lia)) as HS1c.
change (YP06.add_cond n_st1 (mkAC BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (0 - BUFEND))) (SLit 0))) with n_st1c in HS1c. clear HS1.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E0 n_st1c n_st2 _ _ _ HS1c n_run2) HAI1).
intros W2 c2 _ HAI2 (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). cbn [cfg_model] in HAI2. clear HS1c.
rewrite ?wvb_wvb in HAI2 |- *.
assert (VO2 : VO B ly S W sp0 mem md MUT (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms2) mat2 VO1) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF2. intros Hin. destruct (vo_windows_sound E0 n_st1c sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr2. intros Hin. destruct (vo_windows_sound E0 n_st1c sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E0 n_st2 ms2 sp0 HS2 ltac:(vm_compute; reflexivity) Usp0 ltac:(lia)). }
clear VO1 HF2 HFr2.
assert (SRA2' : range_addressable (aview tfibsegs (w_H W) (ms_mem ms2)) SHADOW_OFF (FMT_d) 0) by (intros y Hy; lia).
assert (SHU2' : 0 < 0 -> shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms2)) (FMT_d) 0) by (intros H0; lia).
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy_ext B LAWS AMEMCPY W E0 n_st2 ms2 _ ly S sp0 n_r02 n_rest2 35 RA_FX OSP_FX
(SOff 34 0) (SLit FMT_d) (SLit 0) (wp) (FMT_d) 0
HS2 ltac:(rewrite HBcode; reflexivity) eq_refl Usp0 G3_0 G4_0 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
eq_refl ltac:(cbn [sv_denot]; rewrite Z.add_0_r, A34_0; reflexivity) eq_refl ltac:(reflexivity) eq_refl ltac:(reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(lia)
ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(GEO)
ltac:(left; unfold kLowMemEnd; GEO)
ltac:(first [left; unfold kLowMemEnd; GEO | eapply (vf_stack_amem B); [exact (proj1 VO2) | exact Hstk | exact HtopS | GEO | GEO]])
(vo_rest_disj E0 sp0 ap n_rest2 (wp) 0 ltac:(vm_compute; reflexivity) G12_0 Hap1 Hsp44 ltac:(GEO) ltac:(GEO) ltac:(lia))
(vo_rest_ok E0 sp0 ap n_rest2 ltac:(vm_compute; reflexivity) G12_0 Hap1 Hap2)
(vo_rest_w E0 n_rest2 ltac:(vm_compute; reflexivity))
(proj1 VO2) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VO2)))
ltac:(intros a Ha; lia) SRA2' SHU2'
ltac:(intros a Ha; lia) ltac:(intros y Hy; lia) ltac:(intros H0; lia)) HAI2).
intros W2' c2' _ HAI2' (-> & ms2' & mat2' & -> & HS2' & HAR2' & HP2' & Heff2' & Hfr2' & Hpm2'). cbn [cfg_model] in HAI2'.
rewrite wvb_wvb in HAI2', HAR2' |- *.
change (vf_after_icpt 35 n_st2 RA_FX OSP_FX 0 []) with n_af2 in HS2'.
assert (VO2' : VO B ly S W sp0 mem md MUT (ms_mem ms2') (with_vm_backing (m_vm_lazy md) mat2' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms2) _ (ms_mem ms2') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ ((wp) <= a < (wp) + 0))).
- exact VO2.
- exact HAR2'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat2' mat2 md). apply with_vm_backing_same.
- intros a [Ha|Ha]; [left; unfold vf_band, OSP_FX in *; lia | right; unfold MUT, vo_mut; GEO].
- intros a Hr Hna. apply Hfr2'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm2'. }
remember (havoc E0 35 (map (getr (ms_regs ms2')) CLOB)) as E1 eqn:HE1.
assert (OLD1 : forall j, (j < 35)%nat -> ew E1 j = ew E0 j) by (intros j Hj; rewrite HE1; apply ew_havoc_old; exact Hj).
assert (Usp1 : bv_unsigned (ew E1 2) = sp0) by (rewrite OLD1 by (cbv; lia); exact Usp0).
assert (G3_1 : ew E1 3 = w64 (as_gp B)) by (rewrite OLD1 by (cbv; lia); exact G3_0).
assert (G4_1 : ew E1 4 = w64 (as_tp B)) by (rewrite OLD1 by (cbv; lia); exact G4_0).
assert (G12_1 : bv_unsigned (ew E1 12) = ap) by (rewrite OLD1 by (cbv; lia); exact G12_0).
assert (A34_1 : bv_unsigned (ew E1 34) = wp) by (rewrite OLD1 by (cbv; lia); exact A34_0).
assert (HAE1 : env_agree 32 EA E1)
by (rewrite HE1; apply env_agree_havoc_ge; [cbv; lia | exact HAE0]).
clear HE1 HS2 VO2 SRA2' SHU2' Heff2'.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E1 n_af2 n_st3 _ _ _ HS2' n_run3) HAI2').
intros W3 c3 _ HAI3 (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). cbn [cfg_model] in HAI3. clear HS2'.
rewrite ?wvb_wvb in HAI3 |- *.
assert (VO3 : VO B ly S W sp0 mem md MUT (ms_mem ms3) (with_vm_backing (m_vm_lazy md) mat3 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms3) mat3 VO2') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF3. intros Hin. destruct (vo_windows_sound E1 n_af2 sp0 _ ltac:(vm_compute; reflexivity) Usp1 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr3. intros Hin. destruct (vo_windows_sound E1 n_af2 sp0 _ ltac:(vm_compute; reflexivity) Usp1 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E1 n_st3 ms3 sp0 HS3 ltac:(vm_compute; reflexivity) Usp1 ltac:(lia)). }
clear VO2' HF3 HFr3.
assert (SRA3' : range_addressable (aview tfibsegs (w_H W) (ms_mem ms3)) SHADOW_OFF (68444) 0) by (intros y Hy; lia).
assert (SHU3' : 0 < 0 -> shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms3)) (68444) 0) by (intros H0; lia).
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy_ext B LAWS AMEMCPY W E1 n_st3 ms3 _ ly S sp0 n_r03 n_rest3 51 RA_FX OSP_FX
(SOff 34 0) (SLit 68444) (SLit 0) (wp) (68444) 0
HS3 ltac:(rewrite HBcode; reflexivity) eq_refl Usp1 G3_1 G4_1 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
eq_refl ltac:(cbn [sv_denot]; rewrite Z.add_0_r, A34_1; reflexivity) eq_refl ltac:(reflexivity) eq_refl ltac:(reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(lia)
ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(GEO)
ltac:(left; unfold kLowMemEnd; GEO)
ltac:(first [left; unfold kLowMemEnd; GEO | eapply (vf_stack_amem B); [exact (proj1 VO3) | exact Hstk | exact HtopS | GEO | GEO]])
(vo_rest_disj E1 sp0 ap n_rest3 (wp) 0 ltac:(vm_compute; reflexivity) G12_1 Hap1 Hsp44 ltac:(GEO) ltac:(GEO) ltac:(lia))
(vo_rest_ok E1 sp0 ap n_rest3 ltac:(vm_compute; reflexivity) G12_1 Hap1 Hap2)
(vo_rest_w E1 n_rest3 ltac:(vm_compute; reflexivity))
(proj1 VO3) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VO3)))
ltac:(intros a Ha; lia) SRA3' SHU3'
ltac:(intros a Ha; lia) ltac:(intros y Hy; lia) ltac:(intros H0; lia)) HAI3).
intros W3' c3' _ HAI3' (-> & ms3' & mat3' & -> & HS3' & HAR3' & HP3' & Heff3' & Hfr3' & Hpm3'). cbn [cfg_model] in HAI3'.
rewrite wvb_wvb in HAI3', HAR3' |- *.
change (vf_after_icpt 51 n_st3 RA_FX OSP_FX 0 []) with n_af3 in HS3'.
assert (VO3' : VO B ly S W sp0 mem md MUT (ms_mem ms3') (with_vm_backing (m_vm_lazy md) mat3' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms3) _ (ms_mem ms3') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ ((wp) <= a < (wp) + 0))).
- exact VO3.
- exact HAR3'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat3' mat3 md). apply with_vm_backing_same.
- intros a [Ha|Ha]; [left; unfold vf_band, OSP_FX in *; lia | right; unfold MUT, vo_mut; GEO].
- intros a Hr Hna. apply Hfr3'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm3'. }
remember (havoc E1 51 (map (getr (ms_regs ms3')) CLOB)) as E2 eqn:HE2.
assert (OLD2 : forall j, (j < 51)%nat -> ew E2 j = ew E1 j) by (intros j Hj; rewrite HE2; apply ew_havoc_old; exact Hj).
assert (Usp2 : bv_unsigned (ew E2 2) = sp0) by (rewrite OLD2 by (cbv; lia); exact Usp1).
assert (G3_2 : ew E2 3 = w64 (as_gp B)) by (rewrite OLD2 by (cbv; lia); exact G3_1).
assert (G4_2 : ew E2 4 = w64 (as_tp B)) by (rewrite OLD2 by (cbv; lia); exact G4_1).
assert (G12_2 : bv_unsigned (ew E2 12) = ap) by (rewrite OLD2 by (cbv; lia); exact G12_1).
assert (A34_2 : bv_unsigned (ew E2 34) = wp) by (rewrite OLD2 by (cbv; lia); exact A34_1).
assert (HAE2 : env_agree 32 EA E2)
by (rewrite HE2; apply env_agree_havoc_ge; [cbv; lia | exact HAE1]).
clear HE2 HS3 VO3 SRA3' SHU3' Heff3'.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E2 n_af3 n_st4 _ _ _ HS3' n_run4) HAI3').
intros W4 c4 _ HAI4 (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). cbn [cfg_model] in HAI4. clear HS3'.
rewrite ?wvb_wvb in HAI4 |- *.
assert (VO4 : VO B ly S W sp0 mem md MUT (ms_mem ms4) (with_vm_backing (m_vm_lazy md) mat4 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms4) mat4 VO3') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF4. intros Hin. destruct (vo_windows_sound E2 n_af3 sp0 _ ltac:(vm_compute; reflexivity) Usp2 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr4. intros Hin. destruct (vo_windows_sound E2 n_af3 sp0 _ ltac:(vm_compute; reflexivity) Usp2 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E2 n_st4 ms4 sp0 HS4 ltac:(vm_compute; reflexivity) Usp2 ltac:(lia)). }
clear VO3' HF4 HFr4.
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memset B LAWS AMEMSET W E2 n_st4 ms4 _ ly S sp0 n_r04 n_rest4 67 RA_PAD OSP_PC PAD_OFF 48 1%nat
HS4 ltac:(rewrite HBcode; reflexivity) eq_refl Usp2 G3_2 G4_2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(lia) ltac:(reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_PC; lia) ltac:(unfold OSP_PC, PAD_OFF; lia) ltac:(unfold PAD_OFF; cbn; lia) ltac:(unfold RA_PAD; lia) ltac:(reflexivity)
(vo_rest_ok E2 sp0 ap n_rest4 ltac:(vm_compute; reflexivity) G12_2 Hap1 Hap2)
(vo_rest_w E2 n_rest4 ltac:(vm_compute; reflexivity))
(proj1 VO4) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VO4)))) HAI4).
intros W4' c4' _ HAI4' (-> & ms4' & mat4' & -> & HS4' & HAR4' & HP4' & Hfr4' & Hpm4'). cbn [cfg_model] in HAI4'.
rewrite wvb_wvb in HAI4', HAR4' |- *.
change (vf_after_icpt 67 n_st4 RA_PAD OSP_PC PAD_OFF (repeat 48 1%nat)) with n_af4 in HS4'.
assert (VO4' : VO B ly S W sp0 mem md MUT (ms_mem ms4') (with_vm_backing (m_vm_lazy md) mat4' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms4) _ (ms_mem ms4') _
(fun a => (sp0 + OSP_PC - ESTACK <= a < sp0 + OSP_PC) \/ (sp0 + PAD_OFF <= a < sp0 + PAD_OFF + 1))).
- exact VO4.
- exact HAR4'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat4' mat4 md). apply with_vm_backing_same.
- intros a Ha. left. unfold vf_band, OSP_PC, PAD_OFF in *. lia.
- intros a Hr Hna. apply Hfr4'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; cbn; exact H'].
- exact Hpm4'. }
remember (havoc E2 67 (map (getr (ms_regs ms4')) CLOB)) as E3 eqn:HE3.
assert (OLD3 : forall j, (j < 67)%nat -> ew E3 j = ew E2 j) by (intros j Hj; rewrite HE3; apply ew_havoc_old; exact Hj).
assert (Usp3 : bv_unsigned (ew E3 2) = sp0) by (rewrite OLD3 by (cbv; lia); exact Usp2).
assert (G3_3 : ew E3 3 = w64 (as_gp B)) by (rewrite OLD3 by (cbv; lia); exact G3_2).
assert (G4_3 : ew E3 4 = w64 (as_tp B)) by (rewrite OLD3 by (cbv; lia); exact G4_2).
assert (G12_3 : bv_unsigned (ew E3 12) = ap) by (rewrite OLD3 by (cbv; lia); exact G12_2).
assert (A34_3 : bv_unsigned (ew E3 34) = wp) by (rewrite OLD3 by (cbv; lia); exact A34_2).
assert (HAE3 : env_agree 32 EA E3)
by (rewrite HE3; apply env_agree_havoc_ge; [cbv; lia | exact HAE2]).
clear HE3 HS4 VO4.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E3 n_af4 n_st5 _ _ _ HS4' n_run5) HAI4').
intros W5 c5 _ HAI5 (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). cbn [cfg_model] in HAI5. clear HS4'.
rewrite ?wvb_wvb in HAI5 |- *.
assert (VO5 : VO B ly S W sp0 mem md MUT (ms_mem ms5) (with_vm_backing (m_vm_lazy md) mat5 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms5) mat5 VO4') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF5. intros Hin. destruct (vo_windows_sound E3 n_af4 sp0 _ ltac:(vm_compute; reflexivity) Usp3 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr5. intros Hin. destruct (vo_windows_sound E3 n_af4 sp0 _ ltac:(vm_compute; reflexivity) Usp3 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E3 n_st5 ms5 sp0 HS5 ltac:(vm_compute; reflexivity) Usp3 ltac:(lia)). }
clear VO4' HF5 HFr5.
pose proof (st_ok_add_cond tfibsegs E3 n_st5 _ BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (0 - BUFEND))) (SLit 1) HS5 ltac:(rewrite branch_geu_U, U_neg_off, U_SLit by (rewrite A34_3; unfold M64; lia); rewrite A34_3; change (zcanon 1) with 1; apply Bool.negb_true_iff; apply Z.ltb_ge; lia)) as HS5c.
change (YP06.add_cond n_st5 (mkAC BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (0 - BUFEND))) (SLit 1))) with n_st5c in HS5c. clear HS5.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E3 n_st5c n_st6 _ _ _ HS5c n_run6) HAI5).
intros W6 c6 _ HAI6 (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). cbn [cfg_model] in HAI6. clear HS5c.
rewrite ?wvb_wvb in HAI6 |- *.
assert (VO6 : VO B ly S W sp0 mem md MUT (ms_mem ms6) (with_vm_backing (m_vm_lazy md) mat6 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms6) mat6 VO5) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF6. intros Hin. destruct (vo_windows_sound E3 n_st5c sp0 _ ltac:(vm_compute; reflexivity) Usp3 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr6. intros Hin. destruct (vo_windows_sound E3 n_st5c sp0 _ ltac:(vm_compute; reflexivity) Usp3 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E3 n_st6 ms6 sp0 HS6 ltac:(vm_compute; reflexivity) Usp3 ltac:(lia)). }
clear VO5 HF6 HFr6.
pose proof HS6 as HSc6. destruct HSc6 as (_ & _ & _ & _ & _ & _ & _ & Hmem6 & _). cbn [restrict ms_mem] in Hmem6.
assert (PAD6 : aview tfibsegs (w_H W) (ms_mem ms6) (sp0 + PAD_OFF) = Some 48).
{ replace (sp0 + PAD_OFF) with (sp0 + PAD_OFF + Z.of_nat 0) by lia.
apply (lit_buf_aview W E3 (ms_mem ms6) (ss_mem n_st6) (SOff 2 PAD_OFF) (sp0 + PAD_OFF) 1 [48] Hmem6 ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot]; rewrite Usp3; reflexivity) ltac:(repeat constructor; lia) 0%nat ltac:(lia)). }
clear Hmem6.
destruct (vf_stack_shadow B LAWS W ly S (ms_mem ms6) _ sp0 (sp0 + PAD_OFF) 1 (proj1 VO6) Hstk Htop ltac:(unfold PAD_OFF; lia) ltac:(unfold PAD_OFF; lia) ltac:(lia)) as [SRA6' SHU6'].
destruct (vo_shadow_xfer B ly S W sp0 mem md wp (wp + 2) (ms_mem ms6) _ STDOUT_BUFA STDOUT_BSZ wp 1 VO6 ltac:(lia) Hstk Hra_b Hhull_b
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite KHI; lia)) as [DRA6' DHU6'].
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy_ext B LAWS AMEMCPY W E3 n_st6 ms6 _ ly S sp0 n_r06 n_rest6 83 RA_FX OSP_FX
(SOff 34 0) (SOff 2 PAD_OFF) (SLit 1) (wp) (sp0 + PAD_OFF) 1
HS6 ltac:(rewrite HBcode; reflexivity) eq_refl Usp3 G3_3 G4_3 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
eq_refl ltac:(cbn [sv_denot]; rewrite Z.add_0_r, A34_3; reflexivity) eq_refl ltac:(cbn [sv_denot]; rewrite Usp3; reflexivity) eq_refl ltac:(reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(lia)
ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(GEO)
ltac:(left; unfold kLowMemEnd; GEO)
ltac:(first [left; unfold kLowMemEnd; GEO | eapply (vf_stack_amem B); [exact (proj1 VO6) | exact Hstk | exact HtopS | GEO | GEO]])
(vo_rest_disj E3 sp0 ap n_rest6 (wp) 1 ltac:(vm_compute; reflexivity) G12_3 Hap1 Hsp44 ltac:(GEO) ltac:(GEO) ltac:(lia))
(vo_rest_ok E3 sp0 ap n_rest6 ltac:(vm_compute; reflexivity) G12_3 Hap1 Hap2)
(vo_rest_w E3 n_rest6 ltac:(vm_compute; reflexivity))
(proj1 VO6) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VO6)))
ltac:(intros a Ha; replace a with (sp0 + PAD_OFF) by lia; rewrite PAD6; discriminate) SRA6' SHU6'
ltac:(intros a Ha; split; [apply stdout_buf_writable; lia | apply HBown; right; lia]) ltac:(exact DRA6') ltac:(exact DHU6')) HAI6).
intros W6' c6' _ HAI6' (-> & ms6' & mat6' & -> & HS6' & HAR6' & HP6' & Heff6' & Hfr6' & Hpm6'). cbn [cfg_model] in HAI6'.
rewrite wvb_wvb in HAI6', HAR6' |- *.
change (vf_after_icpt 83 n_st6 RA_FX OSP_FX 0 []) with n_af6 in HS6'.
assert (VO6' : VO B ly S W sp0 mem md MUT (ms_mem ms6') (with_vm_backing (m_vm_lazy md) mat6' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms6) _ (ms_mem ms6') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ ((wp) <= a < (wp) + 1))).
- exact VO6.
- exact HAR6'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat6' mat6 md). apply with_vm_backing_same.
- intros a [Ha|Ha]; [left; unfold vf_band, OSP_FX in *; lia | right; unfold MUT, vo_mut; GEO].
- intros a Hr Hna. apply Hfr6'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm6'. }
assert (BUFA6' : aview tfibsegs (w_H W) (ms_mem ms6') (wp) = Some 48).
{ rewrite <- PAD6, <- (Z.add_0_r wp), <- (Z.add_0_r (sp0 + PAD_OFF)). apply (Heff6' 0). lia. }
remember (havoc E3 83 (map (getr (ms_regs ms6')) CLOB)) as E4 eqn:HE4.
assert (OLD4 : forall j, (j < 83)%nat -> ew E4 j = ew E3 j) by (intros j Hj; rewrite HE4; apply ew_havoc_old; exact Hj).
assert (Usp4 : bv_unsigned (ew E4 2) = sp0) by (rewrite OLD4 by (cbv; lia); exact Usp3).
assert (G3_4 : ew E4 3 = w64 (as_gp B)) by (rewrite OLD4 by (cbv; lia); exact G3_3).
assert (G4_4 : ew E4 4 = w64 (as_tp B)) by (rewrite OLD4 by (cbv; lia); exact G4_3).
assert (G12_4 : bv_unsigned (ew E4 12) = ap) by (rewrite OLD4 by (cbv; lia); exact G12_3).
assert (A34_4 : bv_unsigned (ew E4 34) = wp) by (rewrite OLD4 by (cbv; lia); exact A34_3).
assert (HAE4 : env_agree 32 EA E4)
by (rewrite HE4; apply env_agree_havoc_ge; [cbv; lia | exact HAE3]).
clear HE4 HS6 VO6 SRA6' SHU6' Heff6'.
clear PAD6 DRA6' DHU6'.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E4 n_af6 n_st7 _ _ _ HS6' n_run7) HAI6').
intros W7 c7 _ HAI7 (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). cbn [cfg_model] in HAI7. clear HS6'.
rewrite ?wvb_wvb in HAI7 |- *.
assert (VO7 : VO B ly S W sp0 mem md MUT (ms_mem ms7) (with_vm_backing (m_vm_lazy md) mat7 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms7) mat7 VO6') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF7. intros Hin. destruct (vo_windows_sound E4 n_af6 sp0 _ ltac:(vm_compute; reflexivity) Usp4 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr7. intros Hin. destruct (vo_windows_sound E4 n_af6 sp0 _ ltac:(vm_compute; reflexivity) Usp4 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E4 n_st7 ms7 sp0 HS7 ltac:(vm_compute; reflexivity) Usp4 ltac:(lia)). }
assert (BUFA7 : aview tfibsegs (w_H W) (ms_mem ms7) (wp) = Some 48).
{ rewrite <- BUFA6'. apply aview_eq_of. apply HFr7. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (vo_windows_sound E4 n_af6 sp0 _ ltac:(vm_compute; reflexivity) Usp4 Hin) as [Hw|Hw]; [unfold vf_band in Hw; GEO | unfold vo_file, F_STDOUT, FILE_SZ in Hw; GEO]. }
clear VO6' HF7 HFr7 BUFA6'.
pose proof (st_ok_add_cond tfibsegs E4 n_st7 _ BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (1 - BUFEND))) (SLit 0) HS7 ltac:(rewrite branch_geu_U, U_SLit; change (zcanon 0) with 0; apply Bool.negb_true_iff; apply Z.ltb_ge; pose proof (U_range E4 (SAlu ALU_SUB (SLit 0) (SOff 34 (1 - BUFEND)))); lia)) as HS7c.
change (YP06.add_cond n_st7 (mkAC BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (1 - BUFEND))) (SLit 0))) with n_st7c in HS7c. clear HS7.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E4 n_st7c n_st8 _ _ _ HS7c n_run8) HAI7).
intros W8 c8 _ HAI8 (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). cbn [cfg_model] in HAI8. clear HS7c.
rewrite ?wvb_wvb in HAI8 |- *.
assert (VO8 : VO B ly S W sp0 mem md MUT (ms_mem ms8) (with_vm_backing (m_vm_lazy md) mat8 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms8) mat8 VO7) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF8. intros Hin. destruct (vo_windows_sound E4 n_st7c sp0 _ ltac:(vm_compute; reflexivity) Usp4 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr8. intros Hin. destruct (vo_windows_sound E4 n_st7c sp0 _ ltac:(vm_compute; reflexivity) Usp4 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E4 n_st8 ms8 sp0 HS8 ltac:(vm_compute; reflexivity) Usp4 ltac:(lia)). }
assert (BUFA8 : aview tfibsegs (w_H W) (ms_mem ms8) (wp) = Some 48).
{ rewrite <- BUFA7. apply aview_eq_of. apply HFr8. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (vo_windows_sound E4 n_st7c sp0 _ ltac:(vm_compute; reflexivity) Usp4 Hin) as [Hw|Hw]; [unfold vf_band in Hw; GEO | unfold vo_file, F_STDOUT, FILE_SZ in Hw; GEO]. }
clear VO7 HF8 HFr8 BUFA7.
assert (SRA8' : range_addressable (aview tfibsegs (w_H W) (ms_mem ms8)) SHADOW_OFF (sp0 + PAD_OFF) 0) by (intros y Hy; lia).
assert (SHU8' : 0 < 0 -> shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms8)) (sp0 + PAD_OFF) 0) by (intros H0; lia).
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy_ext B LAWS AMEMCPY W E4 n_st8 ms8 _ ly S sp0 n_r08 n_rest8 99 RA_FX OSP_FX
(SOff 34 1) (SOff 2 PAD_OFF) (SLit 0) (wp + 1) (sp0 + PAD_OFF) 0
HS8 ltac:(rewrite HBcode; reflexivity) eq_refl Usp4 G3_4 G4_4 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
eq_refl ltac:(cbn [sv_denot]; rewrite A34_4; reflexivity) eq_refl ltac:(cbn [sv_denot]; rewrite Usp4; reflexivity) eq_refl ltac:(reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(lia)
ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(GEO)
ltac:(left; unfold kLowMemEnd; GEO)
ltac:(first [left; unfold kLowMemEnd; GEO | eapply (vf_stack_amem B); [exact (proj1 VO8) | exact Hstk | exact HtopS | GEO | GEO]])
(vo_rest_disj E4 sp0 ap n_rest8 (wp + 1) 0 ltac:(vm_compute; reflexivity) G12_4 Hap1 Hsp44 ltac:(GEO) ltac:(GEO) ltac:(lia))
(vo_rest_ok E4 sp0 ap n_rest8 ltac:(vm_compute; reflexivity) G12_4 Hap1 Hap2)
(vo_rest_w E4 n_rest8 ltac:(vm_compute; reflexivity))
(proj1 VO8) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VO8)))
ltac:(intros a Ha; lia) SRA8' SHU8'
ltac:(intros a Ha; lia) ltac:(intros y Hy; lia) ltac:(intros H0; lia)) HAI8).
intros W8' c8' _ HAI8' (-> & ms8' & mat8' & -> & HS8' & HAR8' & HP8' & Heff8' & Hfr8' & Hpm8'). cbn [cfg_model] in HAI8'.
rewrite wvb_wvb in HAI8', HAR8' |- *.
change (vf_after_icpt 99 n_st8 RA_FX OSP_FX 0 []) with n_af8 in HS8'.
assert (VO8' : VO B ly S W sp0 mem md MUT (ms_mem ms8') (with_vm_backing (m_vm_lazy md) mat8' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms8) _ (ms_mem ms8') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ ((wp + 1) <= a < (wp + 1) + 0))).
- exact VO8.
- exact HAR8'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat8' mat8 md). apply with_vm_backing_same.
- intros a [Ha|Ha]; [left; unfold vf_band, OSP_FX in *; lia | right; unfold MUT, vo_mut; GEO].
- intros a Hr Hna. apply Hfr8'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm8'. }
assert (BUFA8' : aview tfibsegs (w_H W) (ms_mem ms8') (wp) = Some 48).
{ rewrite <- BUFA8. apply Hfr8'; [GEO | GEO | GEO]. }
remember (havoc E4 99 (map (getr (ms_regs ms8')) CLOB)) as E5 eqn:HE5.
assert (OLD5 : forall j, (j < 99)%nat -> ew E5 j = ew E4 j) by (intros j Hj; rewrite HE5; apply ew_havoc_old; exact Hj).
assert (Usp5 : bv_unsigned (ew E5 2) = sp0) by (rewrite OLD5 by (cbv; lia); exact Usp4).
assert (G3_5 : ew E5 3 = w64 (as_gp B)) by (rewrite OLD5 by (cbv; lia); exact G3_4).
assert (G4_5 : ew E5 4 = w64 (as_tp B)) by (rewrite OLD5 by (cbv; lia); exact G4_4).
assert (G12_5 : bv_unsigned (ew E5 12) = ap) by (rewrite OLD5 by (cbv; lia); exact G12_4).
assert (A34_5 : bv_unsigned (ew E5 34) = wp) by (rewrite OLD5 by (cbv; lia); exact A34_4).
assert (HAE5 : env_agree 32 EA E5)
by (rewrite HE5; apply env_agree_havoc_ge; [cbv; lia | exact HAE4]).
clear HE5 HS8 VO8 SRA8' SHU8' Heff8' BUFA8.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E5 n_af8 n_st9 _ _ _ HS8' n_run9) HAI8').
intros W9 c9 _ HAI9 (-> & ms9 & mat9 & -> & HS9 & HF9 & HFr9). cbn [cfg_model] in HAI9. clear HS8'.
rewrite ?wvb_wvb in HAI9 |- *.
assert (VO9 : VO B ly S W sp0 mem md MUT (ms_mem ms9) (with_vm_backing (m_vm_lazy md) mat9 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms9) mat9 VO8') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF9. intros Hin. destruct (vo_windows_sound E5 n_af8 sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr9. intros Hin. destruct (vo_windows_sound E5 n_af8 sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E5 n_st9 ms9 sp0 HS9 ltac:(vm_compute; reflexivity) Usp5 ltac:(lia)). }
assert (BUFA9 : aview tfibsegs (w_H W) (ms_mem ms9) (wp) = Some 48).
{ rewrite <- BUFA8'. apply aview_eq_of. apply HFr9. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (vo_windows_sound E5 n_af8 sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin) as [Hw|Hw]; [unfold vf_band in Hw; GEO | unfold vo_file, F_STDOUT, FILE_SZ in Hw; GEO]. }
clear VO8' HF9 HFr9 BUFA8'.
pose proof (st_ok_add_cond tfibsegs E5 n_st9 _ BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (1 - BUFEND))) (SLit 1) HS9 ltac:(rewrite branch_geu_U, U_neg_off, U_SLit by (rewrite A34_5; unfold M64; lia); rewrite A34_5; change (zcanon 1) with 1; apply Bool.negb_true_iff; apply Z.ltb_ge; lia)) as HS9c.
change (YP06.add_cond n_st9 (mkAC BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (1 - BUFEND))) (SLit 1))) with n_st9c in HS9c. clear HS9.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E5 n_st9c n_st10 _ _ _ HS9c n_run10) HAI9).
intros W10 c10 _ HAI10 (-> & ms10 & mat10 & -> & HS10 & HF10 & HFr10). cbn [cfg_model] in HAI10. clear HS9c.
rewrite ?wvb_wvb in HAI10 |- *.
assert (VO10 : VO B ly S W sp0 mem md MUT (ms_mem ms10) (with_vm_backing (m_vm_lazy md) mat10 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms10) mat10 VO9) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF10. intros Hin. destruct (vo_windows_sound E5 n_st9c sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr10. intros Hin. destruct (vo_windows_sound E5 n_st9c sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E5 n_st10 ms10 sp0 HS10 ltac:(vm_compute; reflexivity) Usp5 ltac:(lia)). }
assert (BUFA10 : aview tfibsegs (w_H W) (ms_mem ms10) (wp) = Some 48).
{ rewrite <- BUFA9. apply aview_eq_of. apply HFr10. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (vo_windows_sound E5 n_st9c sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin) as [Hw|Hw]; [unfold vf_band in Hw; GEO | unfold vo_file, F_STDOUT, FILE_SZ in Hw; GEO]. }
clear VO9 HF10 HFr10 BUFA9.
pose proof HS10 as HSc10. destruct HSc10 as (_ & _ & _ & _ & _ & _ & _ & Hmem10 & _). cbn [restrict ms_mem] in Hmem10.
assert (NL10 : aview tfibsegs (w_H W) (ms_mem ms10) 83948 = Some 10).
{ change 83948 with (83948 + Z.of_nat 0).
apply (lit_buf_aview W E5 (ms_mem ms10) (ss_mem n_st10) (SLit 83948) 83948 1 [10] Hmem10 ltac:(vm_compute; reflexivity) eq_refl ltac:(repeat constructor; lia) 0%nat ltac:(lia)). }
clear Hmem10.
destruct (vo_shadow_xfer B ly S W sp0 mem md wp (wp + 2) (ms_mem ms10) _ FMT_d 4 83948 1 VO10 ltac:(lia) Hstk Hra_f Hhull_f
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite KHI; lia)) as [SRA10' SHU10'].
destruct (vo_shadow_xfer B ly S W sp0 mem md wp (wp + 2) (ms_mem ms10) _ STDOUT_BUFA STDOUT_BSZ (wp + 1) 1 VO10 ltac:(lia) Hstk Hra_b Hhull_b
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite KHI; lia)) as [DRA10' DHU10'].
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy_ext B LAWS AMEMCPY W E5 n_st10 ms10 _ ly S sp0 n_r010 n_rest10 115 RA_FX OSP_FX
(SOff 34 1) (SLit 83948) (SLit 1) (wp + 1) (83948) 1
HS10 ltac:(rewrite HBcode; reflexivity) eq_refl Usp5 G3_5 G4_5 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
eq_refl ltac:(cbn [sv_denot]; rewrite A34_5; reflexivity) eq_refl ltac:(reflexivity) eq_refl ltac:(reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(lia)
ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(GEO)
ltac:(left; unfold kLowMemEnd; GEO)
ltac:(first [left; unfold kLowMemEnd; GEO | eapply (vf_stack_amem B); [exact (proj1 VO10) | exact Hstk | exact HtopS | GEO | GEO]])
(vo_rest_disj E5 sp0 ap n_rest10 (wp + 1) 1 ltac:(vm_compute; reflexivity) G12_5 Hap1 Hsp44 ltac:(GEO) ltac:(GEO) ltac:(lia))
(vo_rest_ok E5 sp0 ap n_rest10 ltac:(vm_compute; reflexivity) G12_5 Hap1 Hap2)
(vo_rest_w E5 n_rest10 ltac:(vm_compute; reflexivity))
(proj1 VO10) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VO10)))
ltac:(intros a Ha; replace a with 83948 by lia; rewrite NL10; discriminate) SRA10' SHU10'
ltac:(intros a Ha; split; [apply stdout_buf_writable; lia | apply HBown; right; lia]) ltac:(exact DRA10') ltac:(exact DHU10')) HAI10).
intros W10' c10' _ HAI10' (-> & ms10' & mat10' & -> & HS10' & HAR10' & HP10' & Heff10' & Hfr10' & Hpm10'). cbn [cfg_model] in HAI10'.
rewrite wvb_wvb in HAI10', HAR10' |- *.
change (vf_after_icpt 115 n_st10 RA_FX OSP_FX 0 []) with n_af10 in HS10'.
assert (VO10' : VO B ly S W sp0 mem md MUT (ms_mem ms10') (with_vm_backing (m_vm_lazy md) mat10' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms10) _ (ms_mem ms10') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ ((wp + 1) <= a < (wp + 1) + 1))).
- exact VO10.
- exact HAR10'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat10' mat10 md). apply with_vm_backing_same.
- intros a [Ha|Ha]; [left; unfold vf_band, OSP_FX in *; lia | right; unfold MUT, vo_mut; GEO].
- intros a Hr Hna. apply Hfr10'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm10'. }
assert (BUFA10' : aview tfibsegs (w_H W) (ms_mem ms10') (wp) = Some 48).
{ rewrite <- BUFA10. apply Hfr10'; [GEO | GEO | GEO]. }
assert (BUFB10' : aview tfibsegs (w_H W) (ms_mem ms10') (wp + 1) = Some 10).
{ replace (wp + 1) with (wp + 1 + 0) by lia. rewrite (Heff10' 0) by lia. rewrite Z.add_0_r. exact NL10. }
remember (havoc E5 115 (map (getr (ms_regs ms10')) CLOB)) as E6 eqn:HE6.
assert (OLD6 : forall j, (j < 115)%nat -> ew E6 j = ew E5 j) by (intros j Hj; rewrite HE6; apply ew_havoc_old; exact Hj).
assert (Usp6 : bv_unsigned (ew E6 2) = sp0) by (rewrite OLD6 by (cbv; lia); exact Usp5).
assert (G3_6 : ew E6 3 = w64 (as_gp B)) by (rewrite OLD6 by (cbv; lia); exact G3_5).
assert (G4_6 : ew E6 4 = w64 (as_tp B)) by (rewrite OLD6 by (cbv; lia); exact G4_5).
assert (G12_6 : bv_unsigned (ew E6 12) = ap) by (rewrite OLD6 by (cbv; lia); exact G12_5).
assert (A34_6 : bv_unsigned (ew E6 34) = wp) by (rewrite OLD6 by (cbv; lia); exact A34_5).
assert (HAE6 : env_agree 32 EA E6)
by (rewrite HE6; apply env_agree_havoc_ge; [cbv; lia | exact HAE5]).
clear HE6 HS10 VO10 SRA10' SHU10' Heff10' BUFA10.
clear NL10 DRA10' DHU10'.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E6 n_af10 n_st11 _ _ _ HS10' n_run11) HAI10').
intros W11 c11 _ HAI11 (-> & ms11 & mat11 & -> & HS11 & HF11 & HFr11). cbn [cfg_model] in HAI11. clear HS10'.
rewrite ?wvb_wvb in HAI11 |- *.
assert (VO11 : VO B ly S W sp0 mem md MUT (ms_mem ms11) (with_vm_backing (m_vm_lazy md) mat11 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms11) mat11 VO10') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF11. intros Hin. destruct (vo_windows_sound E6 n_af10 sp0 _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr11. intros Hin. destruct (vo_windows_sound E6 n_af10 sp0 _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E6 n_st11 ms11 sp0 HS11 ltac:(vm_compute; reflexivity) Usp6 ltac:(lia)). }
assert (BUFA11 : aview tfibsegs (w_H W) (ms_mem ms11) (wp) = Some 48).
{ rewrite <- BUFA10'. apply aview_eq_of. apply HFr11. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (vo_windows_sound E6 n_af10 sp0 _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [unfold vf_band in Hw; GEO | unfold vo_file, F_STDOUT, FILE_SZ in Hw; GEO]. }
assert (BUFB11 : aview tfibsegs (w_H W) (ms_mem ms11) (wp + 1) = Some 10).
{ rewrite <- BUFB10'. apply aview_eq_of. apply HFr11. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (vo_windows_sound E6 n_af10 sp0 _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [unfold vf_band in Hw; GEO | unfold vo_file, F_STDOUT, FILE_SZ in Hw; GEO]. }
clear VO10' HF11 HFr11 BUFA10' BUFB10'.
eapply (SRr_srealizes tfibsegs W _
(fun W' c' => W' = W /\ exists mat', c' = mkCfg (mkst (ms_regs ms11) (v_jalr (getr (ms_regs ms11) 1) 0) (ms_mem ms11) (seg_rom tfibsegs))
(with_vm_backing (m_vm_lazy md) mat' md)) T); [ | exact HAI11 | ].
{ eapply (SRr_ret_at tfibsegs tfibmusl_tbl tfibmusl_tbl_ok Hwx W E6); [exact HS11 | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb. split; [reflexivity|]. exists mat'. reflexivity. }
intros WR cR _ HAIR (-> & matR & ->). cbn [cfg_model] in HAIR.
destruct VO11 as (HAR9 & Hsbm9 & Hpb9 & Hfr9 & Hpm9).
rreg HS11 (1%bv : bv 5) Q1.
rewrite OLD6, OLD5, OLD4, OLD3, OLD2, OLD1 in Q1 by (cbv; lia). rewrite E0_1 in Q1.
pose proof (st_ok_restrict_reg tfibsegs (w_H W) E6 _ _ 10 HS11) as Q10. cbn [ms_regs restrict] in Q10.
match type of Q10 with _ = sv_denot _ ?v => let v' := eval vm_compute in v in change v with v' in Q10 end. cbn [sv_denot] in Q10.
replace (v_jalr (getr (ms_regs ms11) 1) 0) with (w64 (raZ regs))
by (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra).
assert (SBMR : same_but_materialized (with_vm_backing (m_vm_lazy md) mat11 md) (with_vm_backing (m_vm_lazy md) matR md))
by (rewrite <- (wvb_collapse (m_vm_lazy md) matR mat11 md); apply with_vm_backing_same).
pose proof (same_but_materialized_frame _ _ SBMR) as MF.
apply (HK (ms_regs ms11) (ms_mem ms11) (with_vm_backing (m_vm_lazy md) matR md)).
* apply (al_frame _ _ LAWS ly S W (ms_mem ms11) _ (ms_mem ms11) _ HAR9); [intros; reflexivity | intros a Hv; exact Hv | apply MF | apply MF | apply MF | exact (AE2y.hs_kept_refl _ _)].
* exact (aregs_preserved_of_st_ok _ E6 _ _ regs _ HS11 HAE6 ltac:(vm_compute; reflexivity)).
* apply with_vm_backing_same.
* rewrite Q10. reflexivity.
* destruct HS11 as (_ & _ & _ & _ & _ & _ & _ & Hmem11 & _).
split.
-- unfold ofile_is, stdout_fields1.
repeat apply Forall_cons; try apply Forall_nil;
(eapply (val_mem_of_lit E6 (mrestrict (w_H W) (ms_mem ms11)) (ss_mem n_st11) _ _ _ Hmem11); vm_compute; reflexivity).
-- exact (val_mem_of_chunk8 E6 (mrestrict (w_H W) (ms_mem ms11)) (ss_mem n_st11) 1%nat (F_STDOUT + 40) (SOff 34 2) (wp + 2) Hmem11
ltac:(vm_compute; reflexivity) ltac:(cbn [sv_denot]; rewrite A34_6; reflexivity) ltac:(lia)).
* exact BUFA11.
* exact BUFB11.
* exact Hfr9.
* exact Hpm9.
* exact HAIR.
Qed.
End S.
End g.
