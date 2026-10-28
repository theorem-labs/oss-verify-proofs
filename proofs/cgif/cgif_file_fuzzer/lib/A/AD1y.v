(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK00 YK15 YK18 YP0n YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YI04 YK04 YA0i YA0n YA0o YA0p YA0q YK09 YA0e YG00 YG01 YG0f YG0n YG0d YCe5.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB12 AB1h AB13 AF0m AD2j AD2i AD1t AE22.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition DRV_IVS : list (Z * Z) := [(0xa2530, 0xa2870); (0xa2948, 0xa2990); (0x5d8650, 0x5d8f38); (0x5f8fe0, 0x5f9200)].
Definition DRVW (a : Z) : bool := existsb (fun iv => (fst iv <=? a) && (a <? snd iv))%bool DRV_IVS.
Lemma DRVW_not_owned : forall a, DRVW a = true -> ~ Exists (in_zr a) Tfib_owned_static.
Proof.
intros a H X. unfold DRVW, DRV_IVS in H. cbn [existsb fst snd] in H. unfold Tfib_owned_static in X.
repeat (apply Exists_cons in X; destruct X as [X|X]; [unfold in_zr in X; cbn [fst snd] in X;
repeat (apply orb_prop in H; destruct H as [H|H]); try discriminate H; apply andb_prop in H; destruct H as [H1 H2]; apply Z.leb_le in H1; apply Z.ltb_lt in H2; lia|]).
inversion X.
Qed.
Lemma DRVW_rw : forall a, DRVW a = true -> 0x9d000 <= a < 0x5fb000.
Proof.
intros a H. unfold DRVW, DRV_IVS in H. cbn [existsb fst snd] in H.
repeat (apply orb_prop in H; destruct H as [H|H]); try discriminate H; apply andb_prop in H; destruct H as [H1 H2]; apply Z.leb_le in H1; apply Z.ltb_lt in H2; lia.
Qed.
Lemma DRVW_lo : forall a, DRVW a = true -> 0xa2530 <= a < 0x5fb000.
Proof.
intros a H. unfold DRVW, DRV_IVS in H. cbn [existsb fst snd] in H.
repeat (apply orb_prop in H; destruct H as [H|H]); try discriminate H; apply andb_prop in H; destruct H as [H1 H2]; apply Z.leb_le in H1; apply Z.ltb_lt in H2; lia.
Qed.
Lemma DRVW_cases : forall a, DRVW a = true -> (0xa2530 <= a < 0xa2870) \/ (0xa2948 <= a < 0xa2990) \/ (0x5d8650 <= a < 0x5d8f38) \/ (0x5f8fe0 <= a < 0x5f9200).
Proof.
intros a H. unfold DRVW, DRV_IVS in H. cbn [existsb fst snd] in H.
repeat (apply orb_prop in H; destruct H as [H|H]); try discriminate H; apply andb_prop in H; destruct H as [H1 H2]; apply Z.leb_le in H1; apply Z.ltb_lt in H2; lia.
Qed.
Definition drv_win_ok (r : YP09.region) : bool :=
((r_whi r <=? r_wlo r)
|| match r_base r with
| Some 0%nat => (- 65536 <=? r_wlo r) && (r_whi r <=? 0)
| None => existsb (fun iv => (fst iv <=? r_wlo r) && (r_whi r <=? snd iv))%bool DRV_IVS
| _ => false
end)%bool.
Lemma in_wrange_drv : forall E rs a, forallb drv_win_ok rs = true -> in_wrange E rs a ->
(bv_unsigned (ew E 0) - 65536 <= a < bv_unsigned (ew E 0)) \/ DRVW a = true.
Proof.
intros E rs a Hok (r & Hin & Ha). pose proof (proj1 (forallb_forall _ _) Hok r Hin) as Hr. unfold drv_win_ok in Hr.
apply orb_prop in Hr as [Hr|Hr]; [apply Z.leb_le in Hr; lia|].
destruct (r_base r) as [[|n]|]; try discriminate Hr; cbn [base_val] in Ha.
- left. apply andb_prop in Hr as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
- right. apply existsb_exists in Hr as (iv & Hiv & Hb). apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
unfold DRVW. apply existsb_exists. exists iv. split; [exact Hiv|]. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma smem_main_win_ok : forall two, forallb drv_win_ok (smem_main two) = true.
Proof. intros [|]; reflexivity. Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis ARL : AR_laws tfibsegs B.
Lemma in_img_rw : forall a, 0x9d000 <= a < 0x5fb000 -> in_img tfibsegs a.
Proof.
intros a Ha. unfold in_img.
assert (E : tfibsegs = [Asan_segment_000; Asan_segment_001;
Asan_segment_002; Asan_segment_003]) by reflexivity.
destruct (Z.lt_ge_cases a 0x9f000).
- exists Asan_segment_002. split; [rewrite E; cbn; tauto | cbn; lia].
- exists Asan_segment_003. split; [rewrite E; cbn; tauto | cbn; lia].
Qed.
Lemma drv_not_owned : forall ly S W mem md a sp0,
AR tfibsegs B ly S W mem md -> sp_window_lo <= sp0 -> YM05.ceil_of_top (sp0 - stack_max_size) ->
(sp0 - 65536 <= a < sp0) \/ DRVW a = true -> ~ aowned B ly S a.
Proof.
intros ly S W mem md a sp0 HAR Hsp HCT Ha Ho.
destruct Ha as [Ha|Ha].
- pose proof (al_owned_low _ _ ARL ly S W mem md a HAR Ho) as L. pose proof (YM05.ceil_le_top _ HCT) as LT.
unfold sp_window_lo, stack_max_size in *. lia.
- pose proof (DRVW_rw a Ha) as R.
apply (DRVW_not_owned a Ha). rewrite <- (ts_owned B HB).
exact (proj1 (al_owned_image _ _ ARL ly S W mem md a HAR (in_img_rw a R)) Ho).
Qed.
Definition in_wrangeb (E : YP0m.env) (rs : smem) (a : Z) : bool :=
existsb (fun r => (base_val E (r_base r) + r_wlo r <=? a) && (a <? base_val E (r_base r) + r_whi r))%bool rs.
Lemma in_wrangeb_false : forall E rs a, in_wrangeb E rs a = false -> ~ in_wrange E rs a.
Proof.
intros E rs a H (r & Hin & Ha). unfold in_wrangeb in H.
assert (X : existsb (fun r => (base_val E (r_base r) + r_wlo r <=? a) && (a <? base_val E (r_base r) + r_whi r))%bool rs = true).
{ apply existsb_exists. exists r. split; [exact Hin|]. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
rewrite X in H. discriminate H.
Qed.
Lemma in_wrangeb_true : forall E rs a, in_wrangeb E rs a = true -> in_wrange E rs a.
Proof.
intros E rs a H. unfold in_wrangeb in H. apply existsb_exists in H as (r & Hin & Hb).
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists r. split; [exact Hin | lia].
Qed.
Lemma AR_after_run : forall ly S W E rs (mem mem' : word -> option byte) md mat,
AR tfibsegs B ly S W mem md ->
forallb drv_win_ok rs = true -> sp_window_lo <= bv_unsigned (ew E 0) -> YM05.ceil_of_top (bv_unsigned (ew E 0) - stack_max_size) ->
frame_of E rs mem mem' ->
(forall a, bv_unsigned (ew E 0) - 65536 <= a < bv_unsigned (ew E 0) -> mem' (Z_to_bv 64 a) <> None) ->
AR tfibsegs B ly S W mem' (with_vm_backing (m_vm_lazy md) mat md).
Proof.
intros ly S W E rs mem mem' md mat HAR Hok Hsp HCT HF Hpres.
apply (al_frame _ _ ARL ly S W mem md mem' (with_vm_backing (m_vm_lazy md) mat md) HAR).
- intros a Ha Ho. unfold aview, mbyte, mrestrict.
assert (Hx : mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ apply HF. intros Hw. apply (drv_not_owned ly S W mem md a (bv_unsigned (ew E 0)) HAR Hsp HCT); [|exact Ho].
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
Lemma AR_model_same : forall ly S W mem md md',
AR tfibsegs B ly S W mem md -> m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
AR tfibsegs B ly S W mem md'.
Proof.
intros ly S W mem md md' (M & L & Bu & MW & HS) Hv Hl He. split; [exact M|]. split; [exact (ALedger_same tfibsegs ly S md md' L Hv Hl He) |].
split; [exact Bu|]. split; [exact (amwf_same md md' Hv Hl MW) | exact HS].
Qed.
Lemma AR_same_but_materialized : forall ly S W mem md md',
AR tfibsegs B ly S W mem md -> same_but_materialized md md' -> AR tfibsegs B ly S W mem md'.
Proof.
intros ly S W mem md md' HAR Hs. rewrite (same_but_materialized_wvb md md' Hs).
apply (AR_model_same ly S W mem md); [exact HAR | reflexivity | apply m_vm_lazy_wvb | unfold eager_used; rewrite m_vm_lazy_wvb; reflexivity].
Qed.
Lemma AR_with_fds : forall ly S W mem md fds, AR tfibsegs B ly S W mem md -> AR tfibsegs B ly S W mem (with_fds fds md).
Proof. intros ly S W mem md fds HAR. apply (AR_model_same ly S W mem md); [exact HAR | reflexivity | reflexivity | reflexivity]. Qed.
Lemma in_img_hull : forall a, 0x10000 <= a < 0x5fb000 -> in_img tfibsegs a.
Proof.
intros a Ha. unfold in_img.
assert (E : tfibsegs = [Asan_segment_000; Asan_segment_001;
Asan_segment_002; Asan_segment_003]) by reflexivity.
rewrite E.
destruct (Z.lt_ge_cases a 0x30000); [exists Asan_segment_000; split; [cbn; tauto | cbn; lia]|].
destruct (Z.lt_ge_cases a 0x9d000); [exists Asan_segment_001; split; [cbn; tauto | cbn; lia]|].
destruct (Z.lt_ge_cases a 0x9f000); [exists Asan_segment_002; split; [cbn; tauto | cbn; lia]|].
exists Asan_segment_003. split; [cbn; tauto | cbn; lia].
Qed.
Lemma not_in_img_high : forall a, 0x5fb000 <= a -> ~ in_img tfibsegs a.
Proof.
intros a Ha (sg & Hin & Hr).
assert (E : tfibsegs = [Asan_segment_000; Asan_segment_001;
Asan_segment_002; Asan_segment_003]) by reflexivity.
rewrite E in Hin. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hr; lia.
Qed.
Lemma apresent_of_writable : forall (H : word -> bool) m a,
0x5fb000 <= a < 2 ^ 64 -> writable_at tfibsegs (mrestrict H m) a -> apresent H m a.
Proof.
intros H m a Ha Hw. unfold writable_at, wview in Hw. unfold apresent.
destruct (mrestrict H m (Z_to_bv 64 a)) as [b|] eqn:Em.
- unfold mrestrict in Em. destruct (H (Z_to_bv 64 a)); [discriminate Em|]. split; [reflexivity | exists b; exact Em].
- exfalso. rewrite (find_segment1_none_outside TSEGS (APC.img_lo TFIB) (APC.img_hi TFIB)) in Hw; [exact (Hw eq_refl) | exact tfib_segs_in_hull |].
right. rewrite u64_lit by lia. cbn. lia.
Qed.
Definition ext_avoids (lo hi : Z) (h : Z * Z) : bool := (fst h + snd h <=? lo) || (hi <=? fst h).
Definition shared_const_chunk (c : YP09.chunk) : bool :=
((YP09.c_off c =? A_GOT_CANARY) && match YP09.c_val c with CImg l => l =? 8 | _ => false end)%bool.
Definition chunk_avoids (l : list (Z * Z)) (c : YP09.chunk) : bool :=
shared_const_chunk c || forallb (ext_avoids (YP09.c_off c) (YP09.c_off c + c_len c)) l.
Lemma shared_const_chunk_sound : forall c, shared_const_chunk c = true -> YP09.c_off c = A_GOT_CANARY /\ c_len c = 8.
Proof.
intros c H. unfold shared_const_chunk in H. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1.
destruct (YP09.c_val c) eqn:Ec; try discriminate H2. apply Z.eqb_eq in H2. unfold c_len. rewrite Ec. cbn. lia.
Qed.
Definition drv_keep_ok (spo : Z) (r : YP09.region) : bool :=
match r_base r with
| Some 0%nat => (spo <=? r_lo r) && ((r_whi r <=? r_wlo r) || ((spo <=? r_wlo r) && (r_whi r <=? r_hi r)))
| Some 6%nat => (0 <=? r_lo r) && (r_whi r <=? r_wlo r)
| Some _ => false
| None => (0x10000 <=? r_lo r) && (r_hi r <=? 0x5fb000)
&& (ext_avoids (r_lo r) (r_hi r) (TFIB_ERRNO, 4) && forallb (chunk_avoids Tfib_owned_static) (r_chunks r))
&& ((r_whi r <=? r_wlo r) || ((0x9d000 <=? r_wlo r) && (r_whi r <=? 0x5fb000)))
end%bool.
Lemma region_ok_kept_chunks : forall E (m m' : word -> option byte) r,
region_ok tfibsegs E m r ->
(forall c i, In c (r_chunks r) -> 0 <= i < c_len c ->
mbyte tfibsegs m' (base_val E (r_base r) + YP09.c_off c + i) = mbyte tfibsegs m (base_val E (r_base r) + YP09.c_off c + i)) ->
(forall o, r_wlo r <= o < r_whi r -> writable_at tfibsegs m' (base_val E (r_base r) + o)) ->
region_ok tfibsegs E m' r.
Proof.
intros E m m' r (B1 & B2 & Wr & C) Hc Hw. split; [exact B1|]. split; [exact B2|]. split; [exact Hw|].
apply Forall_forall. intros c Hin i Hi. pose proof (proj1 (Forall_forall _ _) C c Hin i Hi) as (b & Hb1 & Hb2).
exists b. split; [exact Hb1|]. rewrite (Hc c i Hin Hi). exact Hb2.
Qed.
Lemma regions_wf_In : forall rs r, regions_wf rs = true -> In r rs -> region_wf r = true.
Proof.
induction rs as [|x rs IH]; intros r Hwf Hin; [destruct Hin|]. cbn in Hwf. apply andb_prop in Hwf as [H1 H2].
destruct Hin as [<-|Hin]; [exact H1 | exact (IH r H2 Hin)].
Qed.
Lemma chunk_inside_In : forall r c, region_wf r = true -> In c (r_chunks r) -> r_lo r <= YP09.c_off c /\ YP09.c_off c + c_len c <= r_hi r.
Proof.
intros r c Hwf Hin. unfold region_wf in Hwf. apply andb_prop in Hwf as [_ Hcs].
pose proof (proj1 (forallb_forall _ _) Hcs c Hin) as X. unfold chunk_inside in X.
apply andb_prop in X as [X X3]. apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2. lia.
Qed.
Lemma ext_avoids_sound : forall lo hi l a, forallb (ext_avoids lo hi) l = true -> lo <= a < hi -> ~ Exists (in_zr a) l.
Proof.
intros lo hi l a H Ha X. apply Exists_exists in X as (h & Hin & Hz). pose proof (proj1 (forallb_forall _ _) H h Hin) as Hh.
unfold ext_avoids in Hh. unfold in_zr in Hz. apply orb_prop in Hh as [Hh|Hh]; apply Z.leb_le in Hh; lia.
Qed.
Lemma drv_regions_kept : forall E rs ly S W regs mem md (Eb : Z -> Prop) ly' S' W' regs' mem' md' usp spo,
acall_post tfibsegs B ASTACK ly S W regs mem md Eb ly' S' W' regs' mem' md' ->
AR tfibsegs B ly S W mem md ->
(forall a, Eb a -> a < alloc_ceiling /\ ~ in_img tfibsegs a) ->
regions_wf rs = true ->
Forall (region_ok tfibsegs E (mrestrict (w_H W) mem)) rs ->
forallb (drv_keep_ok spo) rs = true ->
bv_unsigned (ew E 0) = usp -> usp <= bv_unsigned (ew E 6) -> spZ regs = usp + spo -> sp_window_lo - 65536 <= usp + spo -> - 65536 <= spo <= 0 -> sp_window_lo <= usp ->
YM05.ceil_of_top (usp - stack_max_size) ->
Forall (region_ok tfibsegs E (mrestrict (w_H W') mem')) rs.
Proof.
intros E rs ly S W regs mem md Eb ly' S' W' regs' mem' md' usp spo HPOST HAR HEb Hwf Hok Hchk E0 E6 Hsp Hlo Hspo Husp HCT. unfold sp_window_lo in Hlo.
pose proof (YM05.ceil_le_top _ HCT) as LT. unfold stack_max_size in LT.
pose proof HPOST as (HAR' & _ & _ & _ & _ & Hfr & _).
pose proof asan_consts as (C1 & _). pose proof (ts_errno B HB) as Eerr.
apply Forall_forall. intros r Hr.
pose proof (proj1 (Forall_forall _ _) Hok r Hr) as HR. pose proof HR as (B1 & B2 & RW & _).
pose proof (chunk_inside_In r) as CI. specialize (CI) with (1 := regions_wf_In rs r Hwf Hr).
pose proof (proj1 (forallb_forall _ _) Hchk r Hr) as Hc. unfold drv_keep_ok in Hc.
assert (FRAME : forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly' S' a ->
~ (spZ regs - ASTACK <= a < spZ regs) -> ~ (TFIB_ERRNO <= a < TFIB_ERRNO + 4) -> ~ Eb a ->
mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H W) mem) a).
{ intros a Ha Ho Ho' Hs He HE. apply (mbyte_of_aview tfibsegs). apply Hfr; [exact Ha | exact Ho | exact Ho' | | exact HE].
unfold ascratch. rewrite Eerr. tauto. }
assert (HIGH : forall a, usp + spo <= a < 2 ^ 64 ->
mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H W) mem) a
/\ (writable_at tfibsegs (mrestrict (w_H W) mem) a -> writable_at tfibsegs (mrestrict (w_H W') mem') a)).
{ intros a Ha. unfold sp_window_lo in Husp.
assert (Ho : ~ aowned B ly S a) by (intros X; pose proof (al_owned_low _ _ ARL _ _ _ _ _ _ HAR X); unfold sp_window_lo in Husp; lia).
assert (Ho' : ~ aowned B ly' S' a) by (intros X; pose proof (al_owned_low _ _ ARL _ _ _ _ _ _ HAR' X); unfold sp_window_lo in Husp; lia).
assert (EQ : mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H W) mem) a).
{ apply FRAME; [lia | exact Ho | exact Ho' | rewrite Hsp; unfold ASTACK; lia | unfold TFIB_ERRNO; lia | intros X; pose proof (proj1 (HEb a X)); unfold sp_window_lo in Husp; lia]. }
split; [exact EQ|]. intros Hw. apply (apresent_writable tfibsegs).
apply (apresent_transfer tfibsegs (w_H W) (w_H W') mem mem' a);
[lia | apply not_in_img_high; lia | | apply apresent_of_writable; [lia | exact Hw]].
symmetry. unfold aview. rewrite EQ. reflexivity. }
apply (region_ok_kept_chunks E (mrestrict (w_H W) mem) (mrestrict (w_H W') mem') r HR).
- intros c i Hcin Hi. pose proof (CI c Hcin) as [L1 L2].
destruct (r_base r) as [[|[|[|[|[|[|[|n]]]]]]]|] eqn:Hb; try discriminate Hc; cbn [base_val] in B1, B2, RW |- *.
+   apply andb_prop in Hc as [Hc Hcw]. apply Z.leb_le in Hc. rewrite E0 in *. apply (proj1 (HIGH (usp + YP09.c_off c + i) ltac:(lia))).
+   apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1. apply (proj1 (HIGH (bv_unsigned (ew E 6) + YP09.c_off c + i) ltac:(lia))).
+   apply andb_prop in Hc as [Hc Hw]. apply andb_prop in Hc as [Hc Hav]. apply andb_prop in Hc as [Hilo Hihi].
apply Z.leb_le in Hilo. apply Z.leb_le in Hihi.
apply andb_prop in Hav as [Herr Hav]. unfold ext_avoids in Herr. cbn [fst snd] in Herr.
pose proof (proj1 (forallb_forall _ _) Hav c Hcin) as Havc. unfold chunk_avoids in Havc.
apply orb_prop in Havc as [Hsh|Havc].
{
destruct (shared_const_chunk_sound c Hsh) as [Hoff Hlen]. rewrite !Z.add_0_l, Hoff.
apply (canary_got_kept B HB _ _ _ _ _ _ _ _ _ _ i HAR HAR'). lia. }
pose proof (ext_avoids_sound _ _ _ (YP09.c_off c + i) Havc ltac:(lia)) as Hno.
assert (Hne : ~ (TFIB_ERRNO <= YP09.c_off c + i < TFIB_ERRNO + 4)) by (apply orb_prop in Herr as [Herr|Herr]; apply Z.leb_le in Herr; lia).
pose proof (in_img_hull (YP09.c_off c + i) ltac:(lia)) as Himg.
rewrite !Z.add_0_l. apply FRAME; [lia | | | rewrite Hsp; unfold sp_window_lo in Husp; unfold ASTACK; lia | exact Hne
| intros X; exact (proj2 (HEb _ X) Himg)].
* intros X. apply Hno. rewrite <- (ts_owned B HB). exact (proj1 (al_owned_image _ _ ARL _ _ _ _ _ _ HAR Himg) X).
* intros X. apply Hno. rewrite <- (ts_owned B HB). exact (proj1 (al_owned_image _ _ ARL _ _ _ _ _ _ HAR' Himg) X).
- intros o Ho.
destruct (r_base r) as [[|[|[|[|[|[|[|n]]]]]]]|] eqn:Hb; try discriminate Hc; cbn [base_val] in B1, B2, RW |- *.
+ apply andb_prop in Hc as [Hc Hcw]. apply Z.leb_le in Hc. rewrite E0 in *.
apply orb_prop in Hcw as [Hcw|Hcw]; [apply Z.leb_le in Hcw; lia|]. apply andb_prop in Hcw as [Hw1 Hw2].
apply Z.leb_le in Hw1. apply Z.leb_le in Hw2. apply (proj2 (HIGH (usp + o) ltac:(lia))). apply RW. exact Ho.
+ apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc2. lia.
+ apply andb_prop in Hc as [Hc Hw]. apply orb_prop in Hw as [Hw|Hw]; [apply Z.leb_le in Hw; lia|].
apply andb_prop in Hw as [Hw1 Hw2]. apply Z.leb_le in Hw1. apply Z.leb_le in Hw2.
unfold writable_at. rewrite Z.add_0_l. apply tfib_rw_window. rewrite u64_lit by lia. lia.
Qed.
Lemma aregs_regs_preserved : forall regs regs', aregs_preserved regs regs' -> regs_preserved regs regs'.
Proof. intros regs regs' H r Hr. exact (H r Hr). Qed.
Lemma drv_window_after_call : forall ly S W regs mem md (Eb : Z -> Prop) ly' S' W' regs' mem' md' lo,
acall_post tfibsegs B ASTACK ly S W regs mem md Eb ly' S' W' regs' mem' md' ->
AR tfibsegs B ly S W mem md -> (forall a, Eb a -> a < alloc_ceiling /\ ~ in_img tfibsegs a) ->
sp_window_lo - 65536 <= lo -> alloc_ceiling <= lo ->
(forall a, lo <= a < spZ regs -> apresent (w_H W) mem a) ->
forall a, lo <= a < spZ regs -> apresent (w_H W') mem' a.
Proof.
intros ly S W regs mem md Eb ly' S' W' regs' mem' md' lo HPOST HAR HEb Hlo Hcl Hpres a Ha.
pose proof HPOST as (HAR' & _ & _ & _ & _ & Hfr & Hsc). pose proof asan_consts as (C1 & _). pose proof (ts_errno B HB) as Eerr.
unfold sp_window_lo in Hlo. pose proof (u64_range (getr regs 2)) as Hr2. unfold spZ in *.
destruct (Z.lt_ge_cases a (bv_unsigned (getr regs 2) - ASTACK)) as [Hlow|Hhigh]; [| apply Hsc; lia].
apply (apresent_transfer tfibsegs (w_H W) (w_H W') mem mem' a); [lia | apply not_in_img_high; lia | | apply Hpres; lia].
apply Hfr.
- lia.
- intros X. pose proof (al_owned_low _ _ ARL _ _ _ _ _ _ HAR X). lia.
- intros X. pose proof (al_owned_low _ _ ARL _ _ _ _ _ _ HAR' X). lia.
- unfold ascratch, spZ. rewrite Eerr. unfold TFIB_ERRNO. lia.
- intros X. pose proof (proj1 (HEb a X)). lia.
Qed.
Lemma drv_after_call : forall k E ss ms ly S W md (Eb : Z -> Prop) ly' S' W' regs' mem' md' rs retpc usp spo,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_atoms_lt k ss = true ->
regions_wf (WIN spo :: rs) = true -> no_cdata rs = true -> mem_atoms_lt k (WIN spo :: rs) = true -> submem rs (ss_mem ss) ->
sr_get (ss_regs ss) 1 = SLit retpc ->
acall_post tfibsegs B ASTACK ly S W (ms_regs ms) (ms_mem ms) md Eb ly' S' W' regs' mem' md' ->
AR tfibsegs B ly S W (ms_mem ms) md -> (forall a, Eb a -> a < alloc_ceiling /\ ~ in_img tfibsegs a) ->
forallb (drv_keep_ok spo) rs = true ->
bv_unsigned (ew E 0) = usp -> usp <= bv_unsigned (ew E 6) -> spZ (ms_regs ms) = usp + spo -> -4096 <= spo <= 0 -> sp_window_lo <= usp ->
YM05.ceil_of_top (usp - stack_max_size) ->
(forall a, usp - 65536 <= a < usp + spo -> apresent (w_H W) (ms_mem ms) a) ->
st_ok tfibsegs (havoc E k (map (getr regs') CLOB)) (drv_after ss rs k retpc spo)
(restrict (w_H W') (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfibsegs))).
Proof.
intros k E ss ms ly S W md Eb ly' S' W' regs' mem' md' rs retpc usp spo HS Hrv Hat Hwf Hnc Hmat Hsub Hra HPOST HAR HEb Hchk E0 E6 Hsp Hspo Husp HCT Hwin.
pose proof (YM05.ceil_le_top _ HCT) as LT. unfold stack_max_size in LT.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E ss ms HS Hrv) as Hshape.
rewrite Hshape in HS. rewrite restrict_mkst_fx in HS. rewrite restrict_mkst_fx.
unfold drv_after. change (junk_upd k CLOB) with ([] ++ junk_upd k CLOB).
apply (st_ok_splice_havoc tfibsegs k E ss (ms_regs ms) regs' (Z_to_bv 64 (ss_pc ss)) retpc
(mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W') mem') (WIN spo :: rs) [] CLOB HS Hat).
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- reflexivity.
- exact Hmat.
- cbn [map app]. apply regs_preserved_frame. apply aregs_regs_preserved. pose proof HPOST as (_ & _ & _ & HP & _). exact HP.
- constructor.
-
pose proof (st_ok_mem_ok tfibsegs E ss _ HS) as HM. cbn [ms_mem mkst] in HM.
pose proof (mem_ok_sub tfibsegs E _ _ rs Hsub ltac:(cbn in Hwf; apply andb_prop in Hwf; tauto) HM) as HMr.
pose proof HMr as (Hwf' & HokR & Hpd').
pose proof (drv_regions_kept E rs ly S W (ms_regs ms) (ms_mem ms) md Eb ly' S' W' regs' mem' md' usp spo HPOST HAR HEb
Hwf' HokR Hchk E0 E6 Hsp ltac:(unfold sp_window_lo in *; lia) ltac:(lia) Husp HCT) as Hok'.
split; [exact Hwf|]. split.
+ constructor; [|exact Hok'].
pose proof (u64_range (ew E 0)) as HR0. unfold sp_window_lo in Husp.
split; [cbn [base_val r_base r_lo WIN]; lia|]. split; [cbn [base_val r_base r_hi WIN]; lia|].
split; [| constructor].
cbn [base_val r_base r_wlo r_whi WIN]. rewrite E0. intros o Ho. apply (apresent_writable tfibsegs).
apply (drv_window_after_call ly S W (ms_regs ms) (ms_mem ms) md Eb ly' S' W' regs' mem' md' (usp - 65536) HPOST HAR HEb
ltac:(unfold sp_window_lo; lia) ltac:(lia)); [| rewrite Hsp; lia].
intros a Ha. apply Hwin. rewrite Hsp in Ha. lia.
+ split; [|exact Hpd'].
clear - Hchk E0 E6 Hspo Husp. unfold sp_window_lo in Husp.
induction rs as [|r rs IH]; cbn; [exact I|]. cbn in Hchk. apply andb_prop in Hchk as [Hc Hchk].
split; [|exact (IH Hchk)]. unfold extent_disjoint. cbn [r_base r_lo r_hi WIN base_val]. rewrite E0.
unfold drv_keep_ok in Hc. destruct (r_base r) as [[|[|[|[|[|[|[|n]]]]]]]|]; try discriminate Hc; cbn [base_val].
* apply andb_prop in Hc as [Hc _]. apply Z.leb_le in Hc. rewrite E0. left. lia.
* apply andb_prop in Hc as [Hc _]. apply Z.leb_le in Hc. left. lia.
* apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [_ Hc]. apply Z.leb_le in Hc. right. lia.
Qed.
End e.
Lemma tid_of_st_ok : forall E ss ms, st_ok tfibsegs E ss ms ->
atom_lookup (f_atoms (ss_facts ss)) 8%nat = Some (mkAF 1 4194303 0) -> 1 <= bv_unsigned (ew E 8) <= 4194303.
Proof.
intros E ss ms HS Hl. pose proof (st_ok_facts_ok tfibsegs E ss ms HS) as (HA & _).
exact (proj1 (atom_lookup_ok E _ _ _ HA Hl)).
Qed.
End d.
