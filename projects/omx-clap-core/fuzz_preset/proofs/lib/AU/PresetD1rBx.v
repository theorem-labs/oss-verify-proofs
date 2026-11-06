(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the driver-run frame lemmas of fuzz_preset's per-call loop (lib/AU/PresetD1rB.v,
   loop_L_x_B) over preset's second allocator instance ARcf, for the asan-ubsan image. Each lemma is the donor's
   (proofs/cgif/cgif_file_fuzzer/lib/YD1y.v, YE22.v, YD29.v, as copied in lib/Reusable) with cgif's AR replaced by ARcf
   at any hidden-head set Hp, cgif's AR_laws by a Theorem Labs lane's AR_laws_cf (lib/Reusable/YG0dcf.v, used by FIELD NAME)
   and cgif's acall_post by acall_post_cf; the names are the donor's plus `_cf`:
     drv_not_owned_cf          YD1y.v:75     AR_after_run_cf       YD1y.v:101
     canary_got_kept_cf        YE22.v:38     drv_regions_kept_cf   YD1y.v:222
     drv_window_after_call_cf  YD1y.v:290    drv_after_call_cf     YD1y.v:309
   The AR-free lemmas of those files (in_wrange_drv, region_ok_kept_chunks, ...) are used as they stand.
   This file needs no file that imports lib/Reusable/YD2h.v (its closure ends at YD1y / YE22); so_not_owned_cf
   (YD29.v:57), whose STDOUT_MUT is lib/Reusable/YD1w.v's over YD2f's bounds, is in lib/AU/PresetD1rBso.v.
   Nothing in this file is a proof of a function (rule 24: the driver layer of a port). Its asan twin is lib/A/PresetD1rAx.v.
   NOT YET COMPILABLE: it imports lib/Reusable's B driver closure, which carries cgif_file_fuzzer's asan-ubsan
   addresses until a Theorem Labs lane's B relocation (relocB) lands (lib/Reusable/YE20.v:507, YE34.v:39, YF0x.v:35, YCeg.v:60,
   YB13.v:24, YB1h.v:37 fail on FACTS 0b89c6c1bd). The text is lib/A's twin with the B modules; names and argument
   orders are final. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK00 YK15 YK18 YP0n YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YI04 YK04 YA0i YA0n YA0o YA0p YA0q YK09 YA0e YG0v YG00 YG01 YG0f YG0n YG0d YCe5.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB12 YB1h YB13 YF0m YD2j YD2i YD1t YE22 YD1y.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Section e.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis ARL : AR_laws_cf tfibsegs B.

(* AD1y.v:75 *)
Lemma drv_not_owned_cf : forall ly S Hp W mem md a sp0,
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

(* AD1y.v:101 *)
Lemma AR_after_run_cf : forall ly S Hp W E rs (mem mem' : word -> option byte) md mat,
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

(* YG0n.v:535 ALedger_same, for ALedger_cf. *)
Lemma ALedger_cf_same : forall ly S md md',
ALedger_cf tfibsegs ly S md -> m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md ->
eager_used md' = eager_used md -> ALedger_cf tfibsegs ly S md'.
Proof. intros ly S md md' L Hv Hl He. destruct L. constructor; unfold eager_cf in *; rewrite ?Hv, ?Hl, ?He; assumption. Qed.

(* AD1y.v:134 *)
Lemma AR_model_same_cf : forall ly S Hp W mem md md',
ARcf tfibsegs B ly S Hp W mem md -> m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
ARcf tfibsegs B ly S Hp W mem md'.
Proof.
intros ly S Hp W mem md md' (M & L & Bu & MW & HS) Hv Hl He. split; [exact M|]. split; [exact (ALedger_cf_same ly S md md' L Hv Hl He) |].
split; [exact Bu|]. split; [exact (amwf_same md md' Hv Hl MW) | exact HS].
Qed.

(* AD1y.v:141 *)
Lemma AR_same_but_materialized_cf : forall ly S Hp W mem md md',
ARcf tfibsegs B ly S Hp W mem md -> same_but_materialized md md' -> ARcf tfibsegs B ly S Hp W mem md'.
Proof.
intros ly S Hp W mem md md' HAR Hs. rewrite (same_but_materialized_wvb md md' Hs).
apply (AR_model_same_cf ly S Hp W mem md); [exact HAR | reflexivity | apply m_vm_lazy_wvb | unfold eager_used; rewrite m_vm_lazy_wvb; reflexivity].
Qed.

(* AD1y.v:147 *)
Lemma AR_with_fds_cf : forall ly S Hp W mem md fds, ARcf tfibsegs B ly S Hp W mem md -> ARcf tfibsegs B ly S Hp W mem (with_fds fds md).
Proof. intros ly S Hp W mem md fds HAR. apply (AR_model_same_cf ly S Hp W mem md); [exact HAR | reflexivity | reflexivity | reflexivity]. Qed.

(* AE22.v:38: the GOT canary is a constant cell of every ARcf state (ARmcf's amc_const). *)
Lemma canary_got_kept_cf : forall ly S Hp W mem md ly' S' Hp' W' mem' md' i,
ARcf tfibsegs B ly S Hp W mem md -> ARcf tfibsegs B ly' S' Hp' W' mem' md' -> 0 <= i < 8 ->
mbyte tfibsegs (mrestrict (w_H W') mem') (A_GOT_CANARY + i) = mbyte tfibsegs (mrestrict (w_H W) mem) (A_GOT_CANARY + i).
Proof.
intros ly S Hp W mem md ly' S' Hp' W' mem' md' i (M & _) (M' & _) Hi.
pose proof (proj1 (Forall_forall _ _) (amc_const _ _ _ _ _ M) _ (canary_cell_in B HB ly)) as C.
pose proof (proj1 (Forall_forall _ _) (amc_const _ _ _ _ _ M') _ (canary_cell_in B HB ly')) as C'.
unfold cell_holds in C, C'. cbn [c_at c_val c_w z8 c8 aeval] in C, C'.
apply mbyte_of_aview. replace i with (Z.of_nat (Z.to_nat i)) by lia.
rewrite (C (Z.to_nat i) ltac:(lia)), (C' (Z.to_nat i) ltac:(lia)). reflexivity.
Qed.

(* AD1y.v:222 *)
Lemma drv_regions_kept_cf : forall E rs ly S Hp W regs mem md (Eb : Z -> Prop) ly' S' W' regs' mem' md' usp spo,
acall_post_cf tfibsegs B ASTACK ly S Hp W regs mem md Eb ly' S' W' regs' mem' md' ->
ARcf tfibsegs B ly S Hp W mem md ->
(forall a, Eb a -> a < alloc_ceiling /\ ~ in_img tfibsegs a) ->
regions_wf rs = true ->
Forall (region_ok tfibsegs E (mrestrict (w_H W) mem)) rs ->
forallb (drv_keep_ok spo) rs = true ->
bv_unsigned (ew E 0) = usp -> usp <= bv_unsigned (ew E 6) -> spZ regs = usp + spo -> sp_window_lo - 65536 <= usp + spo -> - 65536 <= spo <= 0 -> sp_window_lo <= usp ->
YM05.ceil_of_top (usp - stack_max_size) ->
Forall (region_ok tfibsegs E (mrestrict (w_H W') mem')) rs.
Proof.
intros E rs ly S Hp W regs mem md Eb ly' S' W' regs' mem' md' usp spo HPOST HAR HEb Hwf Hok Hchk E0 E6 Hsp Hlo Hspo Husp HCT. unfold sp_window_lo in Hlo.
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
assert (Ho : ~ aowned B ly S a) by (intros X; pose proof (alc_owned_low _ _ ARL _ _ _ _ _ _ _ HAR X); unfold sp_window_lo in Husp; lia).
assert (Ho' : ~ aowned B ly' S' a) by (intros X; pose proof (alc_owned_low _ _ ARL _ _ _ _ _ _ _ HAR' X); unfold sp_window_lo in Husp; lia).
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
apply (canary_got_kept_cf _ _ _ _ _ _ _ _ _ _ _ _ i HAR HAR'). lia. }
pose proof (ext_avoids_sound _ _ _ (YP09.c_off c + i) Havc ltac:(lia)) as Hno.
assert (Hne : ~ (TFIB_ERRNO <= YP09.c_off c + i < TFIB_ERRNO + 4)) by (apply orb_prop in Herr as [Herr|Herr]; apply Z.leb_le in Herr; lia).
pose proof (in_img_hull (YP09.c_off c + i) ltac:(lia)) as Himg.
rewrite !Z.add_0_l. apply FRAME; [lia | | | rewrite Hsp; unfold sp_window_lo in Husp; unfold ASTACK; lia | exact Hne
| intros X; exact (proj2 (HEb _ X) Himg)].
* intros X. apply Hno. rewrite <- (ts_owned B HB). exact (proj1 (alc_owned_image _ _ ARL _ _ _ _ _ _ _ HAR Himg) X).
* intros X. apply Hno. rewrite <- (ts_owned B HB). exact (proj1 (alc_owned_image _ _ ARL _ _ _ _ _ _ _ HAR' Himg) X).
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

(* AD1y.v:290 *)
Lemma drv_window_after_call_cf : forall ly S Hp W regs mem md (Eb : Z -> Prop) ly' S' W' regs' mem' md' lo,
acall_post_cf tfibsegs B ASTACK ly S Hp W regs mem md Eb ly' S' W' regs' mem' md' ->
ARcf tfibsegs B ly S Hp W mem md -> (forall a, Eb a -> a < alloc_ceiling /\ ~ in_img tfibsegs a) ->
sp_window_lo - 65536 <= lo -> alloc_ceiling <= lo ->
(forall a, lo <= a < spZ regs -> apresent (w_H W) mem a) ->
forall a, lo <= a < spZ regs -> apresent (w_H W') mem' a.
Proof.
intros ly S Hp W regs mem md Eb ly' S' W' regs' mem' md' lo HPOST HAR HEb Hlo Hcl Hpres a Ha.
pose proof HPOST as (HAR' & _ & _ & _ & _ & Hfr & Hsc). pose proof asan_consts as (C1 & _). pose proof (ts_errno B HB) as Eerr.
unfold sp_window_lo in Hlo. pose proof (u64_range (getr regs 2)) as Hr2. unfold spZ in *.
destruct (Z.lt_ge_cases a (bv_unsigned (getr regs 2) - ASTACK)) as [Hlow|Hhigh]; [| apply Hsc; lia].
apply (apresent_transfer tfibsegs (w_H W) (w_H W') mem mem' a); [lia | apply not_in_img_high; lia | | apply Hpres; lia].
apply Hfr.
- lia.
- intros X. pose proof (alc_owned_low _ _ ARL _ _ _ _ _ _ _ HAR X). lia.
- intros X. pose proof (alc_owned_low _ _ ARL _ _ _ _ _ _ _ HAR' X). lia.
- unfold ascratch, spZ. rewrite Eerr. unfold TFIB_ERRNO. lia.
- intros X. pose proof (proj1 (HEb a X)). lia.
Qed.

(* AD1y.v:309 *)
Lemma drv_after_call_cf : forall k E ss ms ly S Hp W md (Eb : Z -> Prop) ly' S' W' regs' mem' md' rs retpc usp spo,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_atoms_lt k ss = true ->
regions_wf (WIN spo :: rs) = true -> no_cdata rs = true -> mem_atoms_lt k (WIN spo :: rs) = true -> submem rs (ss_mem ss) ->
sr_get (ss_regs ss) 1 = SLit retpc ->
acall_post_cf tfibsegs B ASTACK ly S Hp W (ms_regs ms) (ms_mem ms) md Eb ly' S' W' regs' mem' md' ->
ARcf tfibsegs B ly S Hp W (ms_mem ms) md -> (forall a, Eb a -> a < alloc_ceiling /\ ~ in_img tfibsegs a) ->
forallb (drv_keep_ok spo) rs = true ->
bv_unsigned (ew E 0) = usp -> usp <= bv_unsigned (ew E 6) -> spZ (ms_regs ms) = usp + spo -> -4096 <= spo <= 0 -> sp_window_lo <= usp ->
YM05.ceil_of_top (usp - stack_max_size) ->
(forall a, usp - 65536 <= a < usp + spo -> apresent (w_H W) (ms_mem ms) a) ->
st_ok tfibsegs (havoc E k (map (getr regs') CLOB)) (drv_after ss rs k retpc spo)
(restrict (w_H W') (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfibsegs))).
Proof.
intros k E ss ms ly S Hp W md Eb ly' S' W' regs' mem' md' rs retpc usp spo HS Hrv Hat Hwf Hnc Hmat Hsub Hra HPOST HAR HEb Hchk E0 E6 Hsp Hspo Husp HCT Hwin.
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
pose proof (drv_regions_kept_cf E rs ly S Hp W (ms_regs ms) (ms_mem ms) md Eb ly' S' W' regs' mem' md' usp spo HPOST HAR HEb
Hwf' HokR Hchk E0 E6 Hsp ltac:(unfold sp_window_lo in *; lia) ltac:(lia) Husp HCT) as Hok'.
split; [exact Hwf|]. split.
+ constructor; [|exact Hok'].
pose proof (u64_range (ew E 0)) as HR0. unfold sp_window_lo in Husp.
split; [cbn [base_val r_base r_lo WIN]; lia|]. split; [cbn [base_val r_base r_hi WIN]; lia|].
split; [| constructor].
cbn [base_val r_base r_wlo r_whi WIN]. rewrite E0. intros o Ho. apply (apresent_writable tfibsegs).
apply (drv_window_after_call_cf ly S Hp W (ms_regs ms) (ms_mem ms) md Eb ly' S' W' regs' mem' md' (usp - 65536) HPOST HAR HEb
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

(* ---------------------------------------------------------------------- *)
(* The same three lemmas after a free under the re-hide (the call post YGcfRehidePost.acall_post_cf_rh): its view frame
   excepts the set the call may hide, dead_shadow_new ly S S', which lies in the shadow of the application ranges
   (above kLowMemEnd, dead_shadow_new_not_low; below kHighMemBeg, dead_shadow_new_high). So it misses every image
   byte and every stack byte, the only bytes these lemmas read through the frame, and the proofs are the ones above
   with that one more premise discharged. *)
Lemma dsn_not_img : forall ly S S' a, a < 2 ^ 24 -> ~ YGcfRehidePost.dead_shadow_new ly S S' a.
Proof.
intros ly S S' a Ha X. pose proof (YGcfRehidePost.dead_shadow_new_not_low ly S S' a X) as NL. unfold kLowMemEnd in NL. lia.
Qed.

Lemma dsn_not_stack : forall ly S S' a, sp_window_lo - 131072 <= a -> ~ YGcfRehidePost.dead_shadow_new ly S S' a.
Proof. intros ly S S' a Ha. apply YGcfRehidePost.dead_shadow_new_high. unfold sp_window_lo, kHighMemBeg in *. lia. Qed.

Lemma drv_regions_kept_cf_rh : forall E rs ly S Hp W regs mem md (Eb : Z -> Prop) ly' S' W' regs' mem' md' usp spo,
YGcfRehidePost.acall_post_cf_rh tfibsegs B ASTACK ly S Hp W regs mem md Eb ly' S' W' regs' mem' md' ->
ARcf tfibsegs B ly S Hp W mem md ->
(forall a, Eb a -> a < alloc_ceiling /\ ~ in_img tfibsegs a) ->
regions_wf rs = true ->
Forall (region_ok tfibsegs E (mrestrict (w_H W) mem)) rs ->
forallb (drv_keep_ok spo) rs = true ->
bv_unsigned (ew E 0) = usp -> usp <= bv_unsigned (ew E 6) -> spZ regs = usp + spo -> sp_window_lo - 65536 <= usp + spo -> - 65536 <= spo <= 0 -> sp_window_lo <= usp ->
YM05.ceil_of_top (usp - stack_max_size) ->
Forall (region_ok tfibsegs E (mrestrict (w_H W') mem')) rs.
Proof.
intros E rs ly S Hp W regs mem md Eb ly' S' W' regs' mem' md' usp spo HPOST HAR HEb Hwf Hok Hchk E0 E6 Hsp Hlo Hspo Husp HCT.
assert (DSS : forall a, usp + spo <= a -> ~ YGcfRehidePost.dead_shadow_new ly S S' a) by (intros a Ha; apply dsn_not_stack; lia).
unfold sp_window_lo in Hlo.
pose proof (YM05.ceil_le_top _ HCT) as LT. unfold stack_max_size in LT.
pose proof HPOST as (HAR' & _ & _ & _ & _ & Hfr & _).
pose proof asan_consts as (C1 & _). pose proof (ts_errno B HB) as Eerr.
apply Forall_forall. intros r Hr.
pose proof (proj1 (Forall_forall _ _) Hok r Hr) as HR. pose proof HR as (B1 & B2 & RW & _).
pose proof (chunk_inside_In r) as CI. specialize (CI) with (1 := regions_wf_In rs r Hwf Hr).
pose proof (proj1 (forallb_forall _ _) Hchk r Hr) as Hc. unfold drv_keep_ok in Hc.
assert (FRAME : forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly' S' a ->
~ (spZ regs - ASTACK <= a < spZ regs) -> ~ (TFIB_ERRNO <= a < TFIB_ERRNO + 4) -> ~ Eb a ->
~ YGcfRehidePost.dead_shadow_new ly S S' a ->
mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H W) mem) a).
{ intros a Ha Ho Ho' Hs He HE HD. apply (mbyte_of_aview tfibsegs). apply Hfr; [exact Ha | exact Ho | exact Ho' | | exact HE | exact HD].
unfold ascratch. rewrite Eerr. tauto. }
assert (HIGH : forall a, usp + spo <= a < 2 ^ 64 ->
mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H W) mem) a
/\ (writable_at tfibsegs (mrestrict (w_H W) mem) a -> writable_at tfibsegs (mrestrict (w_H W') mem') a)).
{ intros a Ha. unfold sp_window_lo in Husp.
assert (Ho : ~ aowned B ly S a) by (intros X; pose proof (alc_owned_low _ _ ARL _ _ _ _ _ _ _ HAR X); unfold sp_window_lo in Husp; lia).
assert (Ho' : ~ aowned B ly' S' a) by (intros X; pose proof (alc_owned_low _ _ ARL _ _ _ _ _ _ _ HAR' X); unfold sp_window_lo in Husp; lia).
assert (EQ : mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H W) mem) a).
{ apply FRAME; [lia | exact Ho | exact Ho' | rewrite Hsp; unfold ASTACK; lia | unfold TFIB_ERRNO; lia | intros X; pose proof (proj1 (HEb a X)); unfold sp_window_lo in Husp; lia
  | exact (DSS a ltac:(lia))]. }
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
apply (canary_got_kept_cf _ _ _ _ _ _ _ _ _ _ _ _ i HAR HAR'). lia. }
pose proof (ext_avoids_sound _ _ _ (YP09.c_off c + i) Havc ltac:(lia)) as Hno.
assert (Hne : ~ (TFIB_ERRNO <= YP09.c_off c + i < TFIB_ERRNO + 4)) by (apply orb_prop in Herr as [Herr|Herr]; apply Z.leb_le in Herr; lia).
pose proof (in_img_hull (YP09.c_off c + i) ltac:(lia)) as Himg.
rewrite !Z.add_0_l. apply FRAME; [lia | | | rewrite Hsp; unfold sp_window_lo in Husp; unfold ASTACK; lia | exact Hne
| intros X; exact (proj2 (HEb _ X) Himg) | apply dsn_not_img; lia].
* intros X. apply Hno. rewrite <- (ts_owned B HB). exact (proj1 (alc_owned_image _ _ ARL _ _ _ _ _ _ _ HAR Himg) X).
* intros X. apply Hno. rewrite <- (ts_owned B HB). exact (proj1 (alc_owned_image _ _ ARL _ _ _ _ _ _ _ HAR' Himg) X).
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

Lemma drv_window_after_call_cf_rh : forall ly S Hp W regs mem md (Eb : Z -> Prop) ly' S' W' regs' mem' md' lo,
YGcfRehidePost.acall_post_cf_rh tfibsegs B ASTACK ly S Hp W regs mem md Eb ly' S' W' regs' mem' md' ->
ARcf tfibsegs B ly S Hp W mem md -> (forall a, Eb a -> a < alloc_ceiling /\ ~ in_img tfibsegs a) ->
sp_window_lo - 65536 <= lo -> alloc_ceiling <= lo ->
(forall a, lo <= a < spZ regs -> apresent (w_H W) mem a) ->
forall a, lo <= a < spZ regs -> apresent (w_H W') mem' a.
Proof.
intros ly S Hp W regs mem md Eb ly' S' W' regs' mem' md' lo HPOST HAR HEb Hlo Hcl Hpres a Ha.
assert (HD : ~ YGcfRehidePost.dead_shadow_new ly S S' a) by (apply dsn_not_stack; lia).
pose proof HPOST as (HAR' & _ & _ & _ & _ & Hfr & Hsc). pose proof asan_consts as (C1 & _). pose proof (ts_errno B HB) as Eerr.
unfold sp_window_lo in Hlo. pose proof (u64_range (getr regs 2)) as Hr2. unfold spZ in *.
destruct (Z.lt_ge_cases a (bv_unsigned (getr regs 2) - ASTACK)) as [Hlow|Hhigh]; [| apply Hsc; lia].
apply (apresent_transfer tfibsegs (w_H W) (w_H W') mem mem' a); [lia | apply not_in_img_high; lia | | apply Hpres; lia].
apply Hfr.
- lia.
- intros X. pose proof (alc_owned_low _ _ ARL _ _ _ _ _ _ _ HAR X). lia.
- intros X. pose proof (alc_owned_low _ _ ARL _ _ _ _ _ _ _ HAR' X). lia.
- unfold ascratch, spZ. rewrite Eerr. unfold TFIB_ERRNO. lia.
- intros X. pose proof (proj1 (HEb a X)). lia.
- exact HD.
Qed.

Lemma drv_after_call_cf_rh : forall k E ss ms ly S Hp W md (Eb : Z -> Prop) ly' S' W' regs' mem' md' rs retpc usp spo,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_atoms_lt k ss = true ->
regions_wf (WIN spo :: rs) = true -> no_cdata rs = true -> mem_atoms_lt k (WIN spo :: rs) = true -> submem rs (ss_mem ss) ->
sr_get (ss_regs ss) 1 = SLit retpc ->
YGcfRehidePost.acall_post_cf_rh tfibsegs B ASTACK ly S Hp W (ms_regs ms) (ms_mem ms) md Eb ly' S' W' regs' mem' md' ->
ARcf tfibsegs B ly S Hp W (ms_mem ms) md -> (forall a, Eb a -> a < alloc_ceiling /\ ~ in_img tfibsegs a) ->
forallb (drv_keep_ok spo) rs = true ->
bv_unsigned (ew E 0) = usp -> usp <= bv_unsigned (ew E 6) -> spZ (ms_regs ms) = usp + spo -> -4096 <= spo <= 0 -> sp_window_lo <= usp ->
YM05.ceil_of_top (usp - stack_max_size) ->
(forall a, usp - 65536 <= a < usp + spo -> apresent (w_H W) (ms_mem ms) a) ->
st_ok tfibsegs (havoc E k (map (getr regs') CLOB)) (drv_after ss rs k retpc spo)
(restrict (w_H W') (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfibsegs))).
Proof.
intros k E ss ms ly S Hp W md Eb ly' S' W' regs' mem' md' rs retpc usp spo HS Hrv Hat Hwf Hnc Hmat Hsub Hra HPOST HAR HEb Hchk E0 E6 Hsp Hspo Husp HCT Hwin.
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
pose proof (drv_regions_kept_cf_rh E rs ly S Hp W (ms_regs ms) (ms_mem ms) md Eb ly' S' W' regs' mem' md' usp spo HPOST HAR HEb
Hwf' HokR Hchk E0 E6 Hsp ltac:(unfold sp_window_lo in *; lia) ltac:(lia) Husp HCT) as Hok'.
split; [exact Hwf|]. split.
+ constructor; [|exact Hok'].
pose proof (u64_range (ew E 0)) as HR0. unfold sp_window_lo in Husp.
split; [cbn [base_val r_base r_lo WIN]; lia|]. split; [cbn [base_val r_base r_hi WIN]; lia|].
split; [| constructor].
cbn [base_val r_base r_wlo r_whi WIN]. rewrite E0. intros o Ho. apply (apresent_writable tfibsegs).
apply (drv_window_after_call_cf_rh ly S Hp W (ms_regs ms) (ms_mem ms) md Eb ly' S' W' regs' mem' md' (usp - 65536) HPOST HAR HEb
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

(* YCe5.v:322 *)
Lemma sep_blocks_cf : forall ly S Hp W mem md b m p n,
ARcf tfibsegs B ly S Hp W mem md -> In (b, m) (ablocks B ly S) -> In (p, n) (ablocks B ly S) -> (b, m) <> (p, n) ->
zdisjoint (b, req_size m) (p, req_size n).
Proof.
intros ly S Hp W mem md b m p n HAR H1 H2 Hne.
destruct (alc_sep _ _ ARL ly S Hp W mem md HAR) as [Hpw _]. apply pairwise_app_l in Hpw as [Hpw _].
apply (pairwise_zdisjoint_split _ (b, req_size m) (p, req_size n) Hpw).
exact (map_split_2 (fun b0 : Z * Z => (fst b0, req_size (snd b0))) _ _ _ (in_split_2 _ _ _ H1 H2 Hne)).
Qed.

(* YCe5.v:1518 *)
Lemma amem_range_of_block_cf : forall ly S Hp W mem md p m a n,
ARcf tfibsegs B ly S Hp W mem md -> In (p, m) (ablocks B ly S) -> p <= a -> a + n <= p + req_size m -> amem_range a n.
Proof.
intros ly S Hp W mem md p m a n HAR Hin H1 H2.
destruct (alc_blocks _ _ ARL _ _ _ _ _ _ p m HAR Hin) as (_ & _ & Hc & [Hh Hh2] & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold app_addr, in_app, amem_range, ASAN_CEIL, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, kHighShadowEnd, kImgLo in *. lia.
Qed.

(* AD25.v:685, at Hp = []: there the cf shadow law's hidden-head skip hd_skip [] q is 0. *)
Lemma range_addressable_of_block'_cf : forall ly S W mem md q m a n,
ARcf tfibsegs B ly S [] W mem md -> In (q, m) (ablocks B ly S) -> q <= a -> a + n <= q + req_size m ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md q m a n HAR Hin Hpa Han.
destruct (alc_shadow _ _ ARL ly S [] W mem md q m HAR Hin) as [Hbs _].
cbn [hd_skip existsb] in Hbs. rewrite Z.add_0_r, Z.sub_0_r in Hbs.
destruct (Z_lt_le_dec 0 n); [|apply range_addressable_nil; lia].
eapply block_shadow_range; [exact Hbs | lia | lia].
Qed.

(* AD25.v:694 *)
Lemma shadow_hull_vis_of_block'_cf : forall ly S Hp W mem md q m d n,
ARcf tfibsegs B ly S Hp W mem md -> In (q, m) (ablocks B ly S) -> q <= d -> d + n <= q + req_size m -> 0 < n ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) d n.
Proof.
intros ly S Hp W mem md q m d n HAR Hin Hpd Hdn Hn s Hs.
destruct (alc_shadow _ _ ARL ly S Hp W mem md q m HAR Hin) as [_ Hh]. apply Hh.
pose proof (YCe5.shadow_mono q d Hpd) as M1. pose proof (YCe5.shadow_mono (d + n - 1) (q + req_size m - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8) by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.

End e.
End d.
