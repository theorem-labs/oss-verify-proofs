(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1y.v, with its module paths changed and its addresses moved to libreac/fuzz_knock's ASan build; AB1v's tfibsegs is A/AWalkFw0.v's; the image top and image low bounds now cite YImgTop.IMG_TOP and YImgTop.IMG_LO, and the proofs, including the writable-window step that uses AB13's image-top citation, unfold those citations before the arithmetic; the image-hull step after find_segment1_none_outside unfolds YImgTop.IMG_LO / IMG_TOP, which AB12's TFIB.img_lo / img_hi now cite. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/A/AD1y.v (donor image sha256 61768cf4739b), with its module paths changed and its addresses moved to reac-pw/fuzz_pin's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AD1y.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.reac_pw.fuzz_pin.images Require Import Asan.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK00 YK15.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP0n YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YI04 YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.BudgetWit.AW Require Import YA0n_w YA0o_w YA0p_w YA0q_w.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK09.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.BudgetWit.AW Require Import YA0e_w.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG01 YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.BudgetWit.AW Require Import YG0n_w YG0d_w YCe5_w.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import AWalkFw0 AB12.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.BudgetWit.AW Require Import AB1h_w.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import AB13 AF0m AD2j.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.BudgetWit.AW Require Import AD2i_w AD1t_w AE22_w.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition DRV_IVS : list (Z * Z) := [(0x9d5d0, 0x9d910); (0x9df48, 0x9df90); (0x5d3c50, 0x5d4540); (0x5f45e8, 0x5f4808)].
Definition DRVW (a : Z) : bool := existsb (fun iv => (fst iv <=? a) && (a <? snd iv))%bool DRV_IVS.
Lemma DRVW_not_owned : forall a, DRVW a = true -> ~ Exists (in_zr a) Tfib_owned_static.
Proof.
intros a H X. unfold DRVW, DRV_IVS in H. cbn [existsb fst snd] in H. unfold Tfib_owned_static in X.
repeat (apply Exists_cons in X; destruct X as [X|X]; [unfold in_zr in X; cbn [fst snd] in X;
repeat (apply orb_prop in H; destruct H as [H|H]); try discriminate H; apply andb_prop in H; destruct H as [H1 H2]; apply Z.leb_le in H1; apply Z.ltb_lt in H2; lia|]).
inversion X.
Qed.
Lemma DRVW_rw : forall a, DRVW a = true -> 0x97000 <= a < 0x5f6000.
Proof.
intros a H. unfold DRVW, DRV_IVS in H. cbn [existsb fst snd] in H. unfold YImgTop.IMG_TOP.
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
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis ARL : AR_laws tfibsegs B.
Lemma in_img_rw : forall a, 0x97000 <= a < 0x5f6000 -> in_img tfibsegs a.
Proof.
intros a Ha. unfold YImgTop.IMG_TOP in Ha. unfold in_img.
assert (E : tfibsegs = [Asan_segment_000; Asan_segment_001;
Asan_segment_002; Asan_segment_003]) by reflexivity.
destruct (Z.lt_ge_cases a 0x9a000).
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
+ pose proof (DRVW_rw a Hd) as X. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *. clear - Ha X. lia.
Qed.
Lemma apresent_of_writable : forall (H : word -> bool) m a,
0x5f6000 <= a < 2 ^ 64 -> writable_at tfibsegs (mrestrict H m) a -> apresent H m a.
Proof.
intros H m a Ha Hw. unfold YImgTop.IMG_TOP in Ha. unfold writable_at, wview in Hw. unfold apresent.
destruct (mrestrict H m (Z_to_bv 64 a)) as [b|] eqn:Em.
- unfold mrestrict in Em. destruct (H (Z_to_bv 64 a)); [discriminate Em|]. split; [reflexivity | exists b; exact Em].
- exfalso. rewrite (find_segment1_none_outside TSEGS (APC.img_lo TFIB) (APC.img_hi TFIB)) in Hw; [exact (Hw eq_refl) | exact tfib_segs_in_hull |].
right. rewrite u64_lit by lia. cbn. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP. lia.
Qed.
Definition ext_avoids (lo hi : Z) (h : Z * Z) : bool := (fst h + snd h <=? lo) || (hi <=? fst h).
Definition shared_const_chunk (c : YP09.chunk) : bool :=
((YP09.c_off c =? A_GOT_CANARY) && match YP09.c_val c with CImg l => l =? 8 | _ => false end)%bool.
Definition chunk_avoids (l : list (Z * Z)) (c : YP09.chunk) : bool :=
shared_const_chunk c || forallb (ext_avoids (YP09.c_off c) (YP09.c_off c + c_len c)) l.
Definition drv_keep_ok (spo : Z) (r : YP09.region) : bool :=
match r_base r with
| Some 0%nat => (spo <=? r_lo r) && ((r_whi r <=? r_wlo r) || ((spo <=? r_wlo r) && (r_whi r <=? r_hi r)))
| Some 6%nat => (0 <=? r_lo r) && (r_whi r <=? r_wlo r)
| Some _ => false
| None => (0x10000 <=? r_lo r) && (r_hi r <=? 0x5f6000)
&& (ext_avoids (r_lo r) (r_hi r) (TFIB_ERRNO, 4) && forallb (chunk_avoids Tfib_owned_static) (r_chunks r))
&& ((r_whi r <=? r_wlo r) || ((0x97000 <=? r_wlo r) && (r_whi r <=? 0x5f6000)))
end%bool.
End e.
Lemma tid_of_st_ok : forall E ss ms, st_ok tfibsegs E ss ms ->
atom_lookup (f_atoms (ss_facts ss)) 8%nat = Some (mkAF 1 4194303 0) -> 1 <= bv_unsigned (ew E 8) <= 4194303.
Proof.
intros E ss ms HS Hl. pose proof (st_ok_facts_ok tfibsegs E ss ms HS) as (HA & _).
exact (proj1 (atom_lookup_ok E _ _ _ HA Hl)).
Qed.
End d.
