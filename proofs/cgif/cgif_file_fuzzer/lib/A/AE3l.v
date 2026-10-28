(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v YO0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE34 AF0l AE3e AE3f AE3g AE6g AE2p AE3i AE3h AF0m AE22 AF0x AE20 AE2y AE7f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition FMT_refused : Z := 0x196bf.
Definition V_refused : Z := 67108864.
Definition msg_refused : list Z :=
[99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 62; 61; 32; 54; 55; 49; 48; 56; 56; 54; 52;
32; 98; 121; 116; 101; 115; 44; 32; 114; 101; 102; 117; 115; 101; 100; 10].
Definition vr0 : sstate := ss_vf FMT_refused (SLit V_refused).
Definition vr_st1 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL vr0).
Definition vr_zs1 : list Z := [99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 62; 61; 32].
Definition vr_af1 : sstate := Eval vm_compute in vf_after_icpt 34 vr_st1 RA_FX OSP_FX (-352) vr_zs1.
Definition vr_st2 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL vr_af1).
Definition vr_af2 : sstate := Eval vm_compute in vf_after_icpt 50 vr_st2 RA_FX OSP_FX (-338) [].
Definition vr_st3 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL vr_af2).
Definition vr_af3 : sstate := Eval vm_compute in vf_after_icpt 66 vr_st3 RA_FX OSP_FX (-338) [].
Definition vr_st4 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL vr_af3).
Definition vr_zs4 : list Z := [54; 55; 49; 48; 56; 56; 54; 52].
Definition vr_af4 : sstate := Eval vm_compute in vf_after_icpt 82 vr_st4 RA_FX OSP_FX (-338) vr_zs4.
Definition vr_st5 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL vr_af4).
Definition vr_zs5 : list Z := [32; 98; 121; 116; 101; 115; 44; 32; 114; 101; 102; 117; 115; 101; 100; 10].
Definition vr_af5 : sstate := Eval vm_compute in vf_after_icpt 98 vr_st5 RA_FX OSP_FX (-330) vr_zs5.
Definition vr_wx := Eval vm_compute in (wx_step tfibmusl_tbl 114 vr_af5).
Definition vr_st6 : sstate := Eval vm_compute in match vr_wx with Some (s1, _, _, _) => s1 | None => vr_af5 end.
Definition vr_af6 : sstate := Eval vm_compute in match vr_wx with Some (_, s2, _, _) => s2 | None => vr_af5 end.
Definition vr_st7 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL vr_af6).
Definition vr_r01 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem vr_st1).
Definition vr_rest1 : smem := Eval vm_compute in tl (ss_mem vr_st1).
Definition vr_r02 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem vr_st2).
Definition vr_rest2 : smem := Eval vm_compute in tl (ss_mem vr_st2).
Definition vr_r03 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem vr_st3).
Definition vr_rest3 : smem := Eval vm_compute in tl (ss_mem vr_st3).
Definition vr_r04 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem vr_st4).
Definition vr_rest4 : smem := Eval vm_compute in tl (ss_mem vr_st4).
Definition vr_r05 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem vr_st5).
Definition vr_rest5 : smem := Eval vm_compute in tl (ss_mem vr_st5).
Lemma vr_wx_eq : wx_step tfibmusl_tbl 114 vr_af5 = Some (vr_st6, vr_af6, msg_refused, 2).
Proof. vm_compute. reflexivity. Qed.
Lemma vr_run1 : sym_runN tfibsegs tfibmusl_tbl FUEL vr0 = (vr_st1, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma vr_run2 : sym_runN tfibsegs tfibmusl_tbl FUEL vr_af1 = (vr_st2, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma vr_run3 : sym_runN tfibsegs tfibmusl_tbl FUEL vr_af2 = (vr_st3, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma vr_run4 : sym_runN tfibsegs tfibmusl_tbl FUEL vr_af3 = (vr_st4, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma vr_run5 : sym_runN tfibsegs tfibmusl_tbl FUEL vr_af4 = (vr_st5, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma vr_run7 : sym_runN tfibsegs tfibmusl_tbl FUEL vr_af6 = (vr_st7, RS_stopped (SR_jalr (SOff 1 0))). Proof. vm_compute. reflexivity. Qed.
Section S.
Variable B : asyms.
Hypothesis TL : TfibSyms B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Let HBcode := ts_code B TL.
Theorem tfib_vfprintf_refused : forall ly S (W : world tfibsegs) regs mem md ch ap cval T,
ecall_pre tfibsegs B ly S W regs mem md ->
2 ^ 44 <= spZ regs -> ly_stk_lo ly + VF_STK <= spZ regs ->
(forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) ->
getr regs 10 = w64 F_STDERR -> getr regs 11 = w64 FMT_refused -> getr regs 12 = w64 ap ->
spZ regs <= ap -> ap + 8 <= 2 ^ 47 -> ap mod 8 = 0 ->
val_mem tfibsegs (mrestrict (w_H W) mem) ap 8 V_refused ->
stderr_pristine (mrestrict (w_H W) mem) -> (forall a, vf_file a -> ~ aowned B ly S a) ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
ro_img (mrestrict (w_H W) mem) ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF FMT_refused 32 ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) FMT_refused 32 ->
fdchan (Z_to_bv 64 2) ch md -> AI tfibsegs (w_H W) (w_A W) md ->
(forall regs' mem' md',
AR tfibsegs B ly S W mem' md' -> aregs_preserved regs regs' -> same_but_materialized md md' ->
getr regs' 10 = w64 38 ->
stderr_after_vfprintf (mrestrict (w_H W) mem') ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_band (spZ regs) a -> ~ vf_file a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_file a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
AI tfibsegs (w_H W) (w_A W) md' ->
srealizes tfibsegs (cfg_at tfibsegs (raZ regs) regs' mem' md') T) ->
srealizes tfibsegs (cfg_at tfibsegs A_vfprintf regs mem md) (t_emit (map (WriteEv ch) (map (Z_to_bv 8) msg_refused)) T).
Proof.
intros ly S W regs mem md ch ap cval T HPRE Hsp44 Hstk Hpres Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg HFP HFown Hgot Hcan Hcv Hro
Hra_f Hhull_f Hch HAI0 HK.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity. assert (HVF : VF_STK = 9104) by reflexivity.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hsp47 : sp0 <= 2 ^ 47) by lia. assert (HtopS : sp0 < kHighMemEnd) by (rewrite KHI; lia).
unfold cfg_at. change (w64 A_vfprintf) with (Z_to_bv 64 A_vfprintf).
pose proof (vf_entry W regs mem FMT_refused (SLit V_refused) ap V_refused cval Hsp44 Hsp47 Hal16
ltac:(intros a Ha; apply Hpres; exact Ha) Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg ltac:(unfold V_refused; lia)
HFP Hgot Hcan Hcv Hro eq_refl) as HS0.
change (ss_vf FMT_refused (SLit V_refused)) with vr0 in HS0.
remember (Ereg regs [Z_to_bv 64 V_refused; Z_to_bv 64 cval]) as E0 eqn:HE0.
assert (EE : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E0 i = getr regs r)
by (intros i r Hi; subst E0; exact (ew_Ereg_nat regs _ i r Hi)).
pose proof (EE 1%nat (1%bv : bv 5) eq_refl) as E0_1.
assert (Usp0 : bv_unsigned (ew E0 2) = sp0) by (rewrite (EE 2%nat (2%bv : bv 5) eq_refl); reflexivity).
assert (G3_0 : ew E0 3 = w64 (as_gp B)) by (rewrite (EE 3%nat (3%bv : bv 5) eq_refl); exact Hgp).
assert (G4_0 : ew E0 4 = w64 (as_tp B)) by (rewrite (EE 4%nat (4%bv : bv 5) eq_refl); exact Htp).
assert (G12_0 : bv_unsigned (ew E0 12) = ap) by (rewrite (EE 12%nat (12%bv : bv 5) eq_refl), Ha2; apply unsigned_lit_small; lia).
assert (HAE0 : env_agree 32 (Ereg regs [Z_to_bv 64 V_refused; Z_to_bv 64 cval]) E0) by (rewrite HE0; split; [intros i Hi; reflexivity | reflexivity]).
clear HE0 EE.
pose proof (VI_init B ly S W sp0 mem md HAR Hpres) as VI0.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E0 vr0 vr_st1 _ _ _ HS0 vr_run1) HAI0).
intros W1 c1 _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [cfg_model] in HAI1. clear HS0.
rewrite ?wvb_wvb in HAI1 |- *.
assert (VI1 : VI B ly S W sp0 mem md (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms1) mat1 VI0) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF1. intros Hin. destruct (vf_windows_sound E0 vr0 sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin); tauto.
- intros x Hx1 Hx2. apply HFr1. intros Hin. destruct (vf_windows_sound E0 vr0 sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin); tauto.
- apply (vf_band_present W E0 vr_st1 ms1 sp0 HS1 ltac:(vm_compute; reflexivity) Usp0 ltac:(lia)). }
clear VI0 HF1 HFr1.
destruct (vf_shadow_xfer B ly S W sp0 mem md (ms_mem ms1) _ FMT_refused 32 104127 14 VI1 Hstk Hra_f Hhull_f
ltac:(unfold FMT_refused; lia) ltac:(unfold FMT_refused; lia) ltac:(unfold FMT_refused; lia) ltac:(rewrite KHI; unfold FMT_refused; lia)) as [SRA1 SHU1].
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy B LAWS AMEMCPY W E0 vr_st1 ms1 _ ly S sp0 vr_r01 vr_rest1 34 RA_FX OSP_FX (-352) (SLit 104127) (104127) 14 vr_zs1
HS1 ltac:(rewrite HBcode; reflexivity) eq_refl Usp0 G3_0 G4_0 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(reflexivity) eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(cbn; lia) ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(lia) ltac:(cbn; lia) ltac:(unfold OSP_FX; cbn; lia) ltac:(cbn; lia) ltac:(left; unfold kLowMemEnd; cbn; lia)
(vf_rest_ok E0 sp0 ap vr_rest1 ltac:(vm_compute; reflexivity) G12_0 Hap1 Hap2)
(vf_rest_w E0 vr_rest1 ltac:(vm_compute; reflexivity))
(proj1 VI1) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VI1))) SRA1 SHU1) HAI1).
intros W1' c1' _ HAI1' (-> & ms1' & mat1' & -> & HS1' & HAR1' & HP1' & Hfr1' & Hpm1'). cbn [cfg_model] in HAI1'.
rewrite wvb_wvb in HAI1', HAR1' |- *.
change (vf_after_icpt 34 vr_st1 RA_FX OSP_FX (-352) vr_zs1) with vr_af1 in HS1'.
assert (VI1' : VI B ly S W sp0 mem md (ms_mem ms1') (with_vm_backing (m_vm_lazy md) mat1' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms1) _ (ms_mem ms1') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ (sp0 + (-352) <= a < sp0 + (-352) + 14))).
- exact VI1.
- exact HAR1'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat1' mat1 md). apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_FX in *. lia.
- intros a Hr Hna. apply Hfr1'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm1'. }
remember (havoc E0 34 (map (getr (ms_regs ms1')) CLOB)) as E1 eqn:HE1.
assert (OLD1 : forall j, (j < 34)%nat -> ew E1 j = ew E0 j) by (intros j Hj; rewrite HE1; apply ew_havoc_old; exact Hj).
assert (Usp1 : bv_unsigned (ew E1 2) = sp0) by (rewrite OLD1 by (cbv; lia); exact Usp0).
assert (G3_1 : ew E1 3 = w64 (as_gp B)) by (rewrite OLD1 by (cbv; lia); exact G3_0).
assert (G4_1 : ew E1 4 = w64 (as_tp B)) by (rewrite OLD1 by (cbv; lia); exact G4_0).
assert (G12_1 : bv_unsigned (ew E1 12) = ap) by (rewrite OLD1 by (cbv; lia); exact G12_0).
assert (HAE1 : env_agree 32 (Ereg regs [Z_to_bv 64 V_refused; Z_to_bv 64 cval]) E1)
by (rewrite HE1; apply env_agree_havoc_ge; [cbv; lia | exact HAE0]).
clear HE1 HS1 VI1 SRA1 SHU1.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E1 vr_af1 vr_st2 _ _ _ HS1' vr_run2) HAI1').
intros W2 c2 _ HAI2 (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). cbn [cfg_model] in HAI2. clear HS1'.
rewrite ?wvb_wvb in HAI2 |- *.
assert (VI2 : VI B ly S W sp0 mem md (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms2) mat2 VI1') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF2. intros Hin. destruct (vf_windows_sound E1 vr_af1 sp0 _ ltac:(vm_compute; reflexivity) Usp1 Hin); tauto.
- intros x Hx1 Hx2. apply HFr2. intros Hin. destruct (vf_windows_sound E1 vr_af1 sp0 _ ltac:(vm_compute; reflexivity) Usp1 Hin); tauto.
- apply (vf_band_present W E1 vr_st2 ms2 sp0 HS2 ltac:(vm_compute; reflexivity) Usp1 ltac:(lia)). }
clear VI1' HF2 HFr2.
destruct (vf_shadow_xfer B ly S W sp0 mem md (ms_mem ms2) _ FMT_refused 32 104141 0 VI2 Hstk Hra_f Hhull_f
ltac:(unfold FMT_refused; lia) ltac:(unfold FMT_refused; lia) ltac:(unfold FMT_refused; lia) ltac:(rewrite KHI; unfold FMT_refused; lia)) as [SRA2 SHU2].
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy B LAWS AMEMCPY W E1 vr_st2 ms2 _ ly S sp0 vr_r02 vr_rest2 50 RA_FX OSP_FX (-338) (SLit 104141) (104141) 0 (@nil Z)
HS2 ltac:(rewrite HBcode; reflexivity) eq_refl Usp1 G3_1 G4_1 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(reflexivity) eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(cbn; lia) ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(lia) ltac:(cbn; lia) ltac:(unfold OSP_FX; cbn; lia) ltac:(cbn; lia) ltac:(left; unfold kLowMemEnd; cbn; lia)
(vf_rest_ok E1 sp0 ap vr_rest2 ltac:(vm_compute; reflexivity) G12_1 Hap1 Hap2)
(vf_rest_w E1 vr_rest2 ltac:(vm_compute; reflexivity))
(proj1 VI2) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VI2))) SRA2 SHU2) HAI2).
intros W2' c2' _ HAI2' (-> & ms2' & mat2' & -> & HS2' & HAR2' & HP2' & Hfr2' & Hpm2'). cbn [cfg_model] in HAI2'.
rewrite wvb_wvb in HAI2', HAR2' |- *.
change (vf_after_icpt 50 vr_st2 RA_FX OSP_FX (-338) (@nil Z)) with vr_af2 in HS2'.
assert (VI2' : VI B ly S W sp0 mem md (ms_mem ms2') (with_vm_backing (m_vm_lazy md) mat2' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms2) _ (ms_mem ms2') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ (sp0 + (-338) <= a < sp0 + (-338) + 0))).
- exact VI2.
- exact HAR2'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat2' mat2 md). apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_FX in *. lia.
- intros a Hr Hna. apply Hfr2'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm2'. }
remember (havoc E1 50 (map (getr (ms_regs ms2')) CLOB)) as E2 eqn:HE2.
assert (OLD2 : forall j, (j < 50)%nat -> ew E2 j = ew E1 j) by (intros j Hj; rewrite HE2; apply ew_havoc_old; exact Hj).
assert (Usp2 : bv_unsigned (ew E2 2) = sp0) by (rewrite OLD2 by (cbv; lia); exact Usp1).
assert (G3_2 : ew E2 3 = w64 (as_gp B)) by (rewrite OLD2 by (cbv; lia); exact G3_1).
assert (G4_2 : ew E2 4 = w64 (as_tp B)) by (rewrite OLD2 by (cbv; lia); exact G4_1).
assert (G12_2 : bv_unsigned (ew E2 12) = ap) by (rewrite OLD2 by (cbv; lia); exact G12_1).
assert (HAE2 : env_agree 32 (Ereg regs [Z_to_bv 64 V_refused; Z_to_bv 64 cval]) E2)
by (rewrite HE2; apply env_agree_havoc_ge; [cbv; lia | exact HAE1]).
clear HE2 HS2 VI2 SRA2 SHU2.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E2 vr_af2 vr_st3 _ _ _ HS2' vr_run3) HAI2').
intros W3 c3 _ HAI3 (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). cbn [cfg_model] in HAI3. clear HS2'.
rewrite ?wvb_wvb in HAI3 |- *.
assert (VI3 : VI B ly S W sp0 mem md (ms_mem ms3) (with_vm_backing (m_vm_lazy md) mat3 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms3) mat3 VI2') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF3. intros Hin. destruct (vf_windows_sound E2 vr_af2 sp0 _ ltac:(vm_compute; reflexivity) Usp2 Hin); tauto.
- intros x Hx1 Hx2. apply HFr3. intros Hin. destruct (vf_windows_sound E2 vr_af2 sp0 _ ltac:(vm_compute; reflexivity) Usp2 Hin); tauto.
- apply (vf_band_present W E2 vr_st3 ms3 sp0 HS3 ltac:(vm_compute; reflexivity) Usp2 ltac:(lia)). }
clear VI2' HF3 HFr3.
assert (SRA3 : range_addressable (aview tfibsegs (w_H W) (ms_mem ms3)) SHADOW_OFF 68444 0) by (intros y Hy; lia).
assert (SHU3 : 0 < 0 -> shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms3)) 68444 0) by (intros H0; lia).
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy B LAWS AMEMCPY W E2 vr_st3 ms3 _ ly S sp0 vr_r03 vr_rest3 66 RA_FX OSP_FX (-338) (SLit 68444) (68444) 0 (@nil Z)
HS3 ltac:(rewrite HBcode; reflexivity) eq_refl Usp2 G3_2 G4_2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(reflexivity) eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(cbn; lia) ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(lia) ltac:(cbn; lia) ltac:(unfold OSP_FX; cbn; lia) ltac:(cbn; lia) ltac:(left; unfold kLowMemEnd; cbn; lia)
(vf_rest_ok E2 sp0 ap vr_rest3 ltac:(vm_compute; reflexivity) G12_2 Hap1 Hap2)
(vf_rest_w E2 vr_rest3 ltac:(vm_compute; reflexivity))
(proj1 VI3) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VI3))) SRA3 SHU3) HAI3).
intros W3' c3' _ HAI3' (-> & ms3' & mat3' & -> & HS3' & HAR3' & HP3' & Hfr3' & Hpm3'). cbn [cfg_model] in HAI3'.
rewrite wvb_wvb in HAI3', HAR3' |- *.
change (vf_after_icpt 66 vr_st3 RA_FX OSP_FX (-338) (@nil Z)) with vr_af3 in HS3'.
assert (VI3' : VI B ly S W sp0 mem md (ms_mem ms3') (with_vm_backing (m_vm_lazy md) mat3' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms3) _ (ms_mem ms3') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ (sp0 + (-338) <= a < sp0 + (-338) + 0))).
- exact VI3.
- exact HAR3'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat3' mat3 md). apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_FX in *. lia.
- intros a Hr Hna. apply Hfr3'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm3'. }
remember (havoc E2 66 (map (getr (ms_regs ms3')) CLOB)) as E3 eqn:HE3.
assert (OLD3 : forall j, (j < 66)%nat -> ew E3 j = ew E2 j) by (intros j Hj; rewrite HE3; apply ew_havoc_old; exact Hj).
assert (Usp3 : bv_unsigned (ew E3 2) = sp0) by (rewrite OLD3 by (cbv; lia); exact Usp2).
assert (G3_3 : ew E3 3 = w64 (as_gp B)) by (rewrite OLD3 by (cbv; lia); exact G3_2).
assert (G4_3 : ew E3 4 = w64 (as_tp B)) by (rewrite OLD3 by (cbv; lia); exact G4_2).
assert (G12_3 : bv_unsigned (ew E3 12) = ap) by (rewrite OLD3 by (cbv; lia); exact G12_2).
assert (HAE3 : env_agree 32 (Ereg regs [Z_to_bv 64 V_refused; Z_to_bv 64 cval]) E3)
by (rewrite HE3; apply env_agree_havoc_ge; [cbv; lia | exact HAE2]).
clear HE3 HS3 VI3 SRA3 SHU3.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E3 vr_af3 vr_st4 _ _ _ HS3' vr_run4) HAI3').
intros W4 c4 _ HAI4 (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). cbn [cfg_model] in HAI4. clear HS3'.
rewrite ?wvb_wvb in HAI4 |- *.
assert (VI4 : VI B ly S W sp0 mem md (ms_mem ms4) (with_vm_backing (m_vm_lazy md) mat4 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms4) mat4 VI3') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF4. intros Hin. destruct (vf_windows_sound E3 vr_af3 sp0 _ ltac:(vm_compute; reflexivity) Usp3 Hin); tauto.
- intros x Hx1 Hx2. apply HFr4. intros Hin. destruct (vf_windows_sound E3 vr_af3 sp0 _ ltac:(vm_compute; reflexivity) Usp3 Hin); tauto.
- apply (vf_band_present W E3 vr_st4 ms4 sp0 HS4 ltac:(vm_compute; reflexivity) Usp3 ltac:(lia)). }
clear VI3' HF4 HFr4.
destruct (vf_stack_shadow B LAWS W ly S (ms_mem ms4) _ sp0 ((sp0 - 744)) 8 (proj1 VI4) Hstk Htop ltac:(lia) ltac:(lia) ltac:(lia)) as [SRA4 SHU4].
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy B LAWS AMEMCPY W E3 vr_st4 ms4 _ ly S sp0 vr_r04 vr_rest4 82 RA_FX OSP_FX (-338) (SOff 2 (-744)) ((sp0 - 744)) 8 vr_zs4
HS4 ltac:(rewrite HBcode; reflexivity) eq_refl Usp3 G3_3 G4_3 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:((cbn [sv_denot]; rewrite Usp3; reflexivity)) eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(cbn; lia) ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(lia) ltac:(cbn; lia) ltac:(unfold OSP_FX; cbn; lia) ltac:(cbn; lia)
ltac:(eapply (vf_stack_amem B); [exact (proj1 VI4) | exact Hstk | exact HtopS | unfold VF_STK; lia | cbn; lia])
(vf_rest_ok E3 sp0 ap vr_rest4 ltac:(vm_compute; reflexivity) G12_3 Hap1 Hap2)
(vf_rest_w E3 vr_rest4 ltac:(vm_compute; reflexivity))
(proj1 VI4) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VI4))) SRA4 SHU4) HAI4).
intros W4' c4' _ HAI4' (-> & ms4' & mat4' & -> & HS4' & HAR4' & HP4' & Hfr4' & Hpm4'). cbn [cfg_model] in HAI4'.
rewrite wvb_wvb in HAI4', HAR4' |- *.
change (vf_after_icpt 82 vr_st4 RA_FX OSP_FX (-338) vr_zs4) with vr_af4 in HS4'.
assert (VI4' : VI B ly S W sp0 mem md (ms_mem ms4') (with_vm_backing (m_vm_lazy md) mat4' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms4) _ (ms_mem ms4') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ (sp0 + (-338) <= a < sp0 + (-338) + 8))).
- exact VI4.
- exact HAR4'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat4' mat4 md). apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_FX in *. lia.
- intros a Hr Hna. apply Hfr4'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm4'. }
remember (havoc E3 82 (map (getr (ms_regs ms4')) CLOB)) as E4 eqn:HE4.
assert (OLD4 : forall j, (j < 82)%nat -> ew E4 j = ew E3 j) by (intros j Hj; rewrite HE4; apply ew_havoc_old; exact Hj).
assert (Usp4 : bv_unsigned (ew E4 2) = sp0) by (rewrite OLD4 by (cbv; lia); exact Usp3).
assert (G3_4 : ew E4 3 = w64 (as_gp B)) by (rewrite OLD4 by (cbv; lia); exact G3_3).
assert (G4_4 : ew E4 4 = w64 (as_tp B)) by (rewrite OLD4 by (cbv; lia); exact G4_3).
assert (G12_4 : bv_unsigned (ew E4 12) = ap) by (rewrite OLD4 by (cbv; lia); exact G12_3).
assert (HAE4 : env_agree 32 (Ereg regs [Z_to_bv 64 V_refused; Z_to_bv 64 cval]) E4)
by (rewrite HE4; apply env_agree_havoc_ge; [cbv; lia | exact HAE3]).
clear HE4 HS4 VI4 SRA4 SHU4.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E4 vr_af4 vr_st5 _ _ _ HS4' vr_run5) HAI4').
intros W5 c5 _ HAI5 (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). cbn [cfg_model] in HAI5. clear HS4'.
rewrite ?wvb_wvb in HAI5 |- *.
assert (VI5 : VI B ly S W sp0 mem md (ms_mem ms5) (with_vm_backing (m_vm_lazy md) mat5 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms5) mat5 VI4') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF5. intros Hin. destruct (vf_windows_sound E4 vr_af4 sp0 _ ltac:(vm_compute; reflexivity) Usp4 Hin); tauto.
- intros x Hx1 Hx2. apply HFr5. intros Hin. destruct (vf_windows_sound E4 vr_af4 sp0 _ ltac:(vm_compute; reflexivity) Usp4 Hin); tauto.
- apply (vf_band_present W E4 vr_st5 ms5 sp0 HS5 ltac:(vm_compute; reflexivity) Usp4 ltac:(lia)). }
clear VI4' HF5 HFr5.
destruct (vf_shadow_xfer B ly S W sp0 mem md (ms_mem ms5) _ FMT_refused 32 104143 16 VI5 Hstk Hra_f Hhull_f
ltac:(unfold FMT_refused; lia) ltac:(unfold FMT_refused; lia) ltac:(unfold FMT_refused; lia) ltac:(rewrite KHI; unfold FMT_refused; lia)) as [SRA5 SHU5].
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy B LAWS AMEMCPY W E4 vr_st5 ms5 _ ly S sp0 vr_r05 vr_rest5 98 RA_FX OSP_FX (-330) (SLit 104143) (104143) 16 vr_zs5
HS5 ltac:(rewrite HBcode; reflexivity) eq_refl Usp4 G3_4 G4_4 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(reflexivity) eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(cbn; lia) ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(lia) ltac:(cbn; lia) ltac:(unfold OSP_FX; cbn; lia) ltac:(cbn; lia) ltac:(left; unfold kLowMemEnd; cbn; lia)
(vf_rest_ok E4 sp0 ap vr_rest5 ltac:(vm_compute; reflexivity) G12_4 Hap1 Hap2)
(vf_rest_w E4 vr_rest5 ltac:(vm_compute; reflexivity))
(proj1 VI5) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VI5))) SRA5 SHU5) HAI5).
intros W5' c5' _ HAI5' (-> & ms5' & mat5' & -> & HS5' & HAR5' & HP5' & Hfr5' & Hpm5'). cbn [cfg_model] in HAI5'.
rewrite wvb_wvb in HAI5', HAR5' |- *.
change (vf_after_icpt 98 vr_st5 RA_FX OSP_FX (-330) vr_zs5) with vr_af5 in HS5'.
assert (VI5' : VI B ly S W sp0 mem md (ms_mem ms5') (with_vm_backing (m_vm_lazy md) mat5' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms5) _ (ms_mem ms5') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ (sp0 + (-330) <= a < sp0 + (-330) + 16))).
- exact VI5.
- exact HAR5'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat5' mat5 md). apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_FX in *. lia.
- intros a Hr Hna. apply Hfr5'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm5'. }
remember (havoc E4 98 (map (getr (ms_regs ms5')) CLOB)) as E5 eqn:HE5.
assert (OLD5 : forall j, (j < 98)%nat -> ew E5 j = ew E4 j) by (intros j Hj; rewrite HE5; apply ew_havoc_old; exact Hj).
assert (Usp5 : bv_unsigned (ew E5 2) = sp0) by (rewrite OLD5 by (cbv; lia); exact Usp4).
assert (G3_5 : ew E5 3 = w64 (as_gp B)) by (rewrite OLD5 by (cbv; lia); exact G3_4).
assert (G4_5 : ew E5 4 = w64 (as_tp B)) by (rewrite OLD5 by (cbv; lia); exact G4_4).
assert (G12_5 : bv_unsigned (ew E5 12) = ap) by (rewrite OLD5 by (cbv; lia); exact G12_4).
assert (HAE5 : env_agree 32 (Ereg regs [Z_to_bv 64 V_refused; Z_to_bv 64 cval]) E5)
by (rewrite HE5; apply env_agree_havoc_ge; [cbv; lia | exact HAE4]).
clear HE5 HS5 VI5 SRA5 SHU5.
eapply (srz_stdio_writev_by_run tfibmusl_tbl W E5 vr_af5 ms5' _ ch 114 vr_st6 vr_af6 msg_refused 2 T tfibmusl_tbl_ok HS5' HAI5' vr_wx_eq).
{ eapply fdchan_sbm; [exact Hch | apply with_vm_backing_same]. }
intros ms6 ws6 mat6 HS6 HF6 HFr6 _ _ HAI6. rewrite ?wvb_wvb in HAI6 |- *.
assert (VI6 : VI B ly S W sp0 mem md (ms_mem ms6) (with_vm_backing (m_vm_lazy md) mat6 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms6) mat6 VI5') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF6. intros Hin. destruct (vf_windows_sound E5 vr_af5 sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin); tauto.
- intros x Hx1 Hx2. apply HFr6. intros Hin. destruct (vf_windows_sound E5 vr_af5 sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin); tauto.
- apply (vf_band_present W (havoc E5 114 ws6) vr_af6 ms6 sp0 HS6 ltac:(vm_compute; reflexivity)); [|lia].
rewrite ew_havoc_old by (cbv; lia). exact Usp5. }
remember (havoc E5 114 ws6) as E6 eqn:HE6.
assert (OLD6 : forall j, (j < 114)%nat -> ew E6 j = ew E5 j) by (intros j Hj; rewrite HE6; apply ew_havoc_old; exact Hj).
assert (Usp6 : bv_unsigned (ew E6 2) = sp0) by (rewrite OLD6 by (cbv; lia); exact Usp5).
assert (HAE6 : env_agree 32 (Ereg regs [Z_to_bv 64 V_refused; Z_to_bv 64 cval]) E6)
by (rewrite HE6; apply env_agree_havoc_ge; [cbv; lia | exact HAE5]).
clear HE6 HS5' VI5' HF6 HFr6.
eapply (SRr_srealizes tfibsegs W _ _ T (vf_phase W E6 vr_af6 vr_st7 _ _ _ HS6 vr_run7) HAI6).
intros W7 c7 _ HAI7 (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). cbn [cfg_model] in HAI7. rewrite ?wvb_wvb in HAI7 |- *.
assert (VI7 : VI B ly S W sp0 mem md (ms_mem ms7) (with_vm_backing (m_vm_lazy md) mat7 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms7) mat7 VI6) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF7. intros Hin. destruct (vf_windows_sound E6 vr_af6 sp0 _ ltac:(vm_compute; reflexivity) Usp6 Hin); tauto.
- intros x Hx1 Hx2. apply HFr7. intros Hin. destruct (vf_windows_sound E6 vr_af6 sp0 _ ltac:(vm_compute; reflexivity) Usp6 Hin); tauto.
- apply (vf_band_present W E6 vr_st7 ms7 sp0 HS7 ltac:(vm_compute; reflexivity) Usp6 ltac:(lia)). }
clear VI6 HF7 HFr7 HS6.
eapply (SRr_srealizes tfibsegs W _
(fun W' c' => W' = W /\ exists mat', c' = mkCfg (mkst (ms_regs ms7) (v_jalr (getr (ms_regs ms7) 1) 0) (ms_mem ms7) (seg_rom tfibsegs))
(with_vm_backing (m_vm_lazy md) mat' md)) T); [ | exact HAI7 | ].
{ eapply (SRr_ret_at tfibsegs tfibmusl_tbl tfibmusl_tbl_ok Hwx W E6); [exact HS7 | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb. split; [reflexivity|]. exists mat'. reflexivity. }
intros W8 c8 _ HAI8 (-> & mat8 & ->). cbn [cfg_model] in HAI8.
destruct VI7 as (HAR7 & Hsbm7 & Hpb7 & Hfr7 & Hpm7).
rreg HS7 (1%bv : bv 5) Q1. rreg HS7 (10%bv : bv 5) Q10.
rewrite OLD6, OLD5, OLD4, OLD3, OLD2, OLD1 in Q1 by (cbv; lia). rewrite E0_1 in Q1.
replace (v_jalr (getr (ms_regs ms7) 1) 0) with (w64 (raZ regs))
by (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra).
assert (SBM78 : same_but_materialized (with_vm_backing (m_vm_lazy md) mat7 md) (with_vm_backing (m_vm_lazy md) mat8 md))
by (rewrite <- (wvb_collapse (m_vm_lazy md) mat8 mat7 md); apply with_vm_backing_same).
pose proof (same_but_materialized_frame _ _ SBM78) as MF.
apply (HK (ms_regs ms7) (ms_mem ms7) (with_vm_backing (m_vm_lazy md) mat8 md)).
- apply (al_frame _ _ LAWS ly S W (ms_mem ms7) _ (ms_mem ms7) _ HAR7); [intros; reflexivity | intros a Hv; exact Hv | apply MF | apply MF | apply MF | exact (AE2y.hs_kept_refl _ _)].
- exact (aregs_preserved_of_st_ok _ E6 _ _ regs [Z_to_bv 64 V_refused; Z_to_bv 64 cval] HS7 HAE6 ltac:(vm_compute; reflexivity)).
- apply with_vm_backing_same.
- rewrite Q10. reflexivity.
- destruct HS7 as (_ & _ & _ & _ & _ & _ & _ & Hmem7 & _).
unfold stderr_after_vfprintf, file_is, stderr_fields_after_vf.
repeat apply Forall_cons; try apply Forall_nil;
(eapply (val_mem_of_lit E6 (mrestrict (w_H W) (ms_mem ms7)) (ss_mem vr_st7) _ _ _ Hmem7); vm_compute; reflexivity).
- exact Hfr7.
- exact Hpm7.
- exact HAI8.
Qed.
End S.
End b.
