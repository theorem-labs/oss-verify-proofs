(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbk AC8a AC8j ACbc ACbf ACbd ACab ACam ACai ACaj ACak ACan ACap.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00 YI0j YI0k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACah.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC7y YC85 YC88.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACb6 ACba AC9z ACa3 ACa4 ACa5 ACa6 ACa7.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Fixpoint out_wins (E : env) (rs : smem) (a : Z) : Prop :=
match rs with
| [] => True
| r :: rs' => (YP09.r_whi r <= YP09.r_wlo r \/
~ (base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r)) /\ out_wins E rs' a
end.
Lemma out_wins_not_in_wrange : forall E rs a, out_wins E rs a -> ~ in_wrange E rs a.
Proof.
induction rs as [|r rs IH]; intros a H (rg & Hin & Hrg); [destruct Hin|].
destruct H as [Hr Hrest]. destruct Hin as [<- | Hin]; [destruct Hr as [Hr | Hr]; [lia | exact (Hr Hrg)]|].
exact (IH a Hrest (ex_intro _ rg (conj Hin Hrg))).
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section f.
Context {PI : PAImg lib_asan3_1_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
Lemma aview_kept_wins : forall E rs H (m m' : word -> option byte),
frame_of E rs (mrestrict H m) (mrestrict H m') ->
forall a, 0 <= a < 2 ^ 64 -> out_wins E rs a -> aview SEGS H m' a = aview SEGS H m a.
Proof. intros E rs H m m' HF a Ha Ho. exact (aview_kept_out E rs H m m' HF a Ha (out_wins_not_in_wrange E rs a Ho)). Qed.
End f.
End d.
Ltac xframe_wins HFr AG Hn :=
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict ?Hh ?m0) (mrestrict _ ?m1) =>
pose proof (aview_kept_wins Ef rs Hh m0 m1 HFr) as Hn;
let rs1 := eval vm_compute in rs in change rs with rs1 in Hn;
cbn [out_wins YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hn; evalE_in AG Hn end.
Lemma land2_cases : forall x, 0 <= x -> Z.land x 2 = 0 \/ Z.land x 2 = 2.
Proof.
intros x Hx. pose proof (Z_land_upper x 2 ltac:(lia)) as Hu.
assert (He : Z.land (Z.land x 2) 1 = 0) by (rewrite <- Z.land_assoc; change (Z.land 2 1) with 0; apply Z.land_0_r).
rewrite land1_bit_t in He by (apply Z.land_nonneg; lia).
set (v := Z.land x 2) in *. assert (Hv : v = 0 \/ v = 1 \/ v = 2) by lia.
destruct Hv as [Hv|[Hv|Hv]]; rewrite Hv in He |- *; [left; reflexivity | discriminate He | right; reflexivity].
Qed.
Lemma flag2_land : forall x, 0 <= x -> YO07.flag x 2 = negb (Z.land x 2 =? 0).
Proof. intros x Hx. reflexivity. Qed.
Lemma xb_packed : forall E a b pkl fa, ew E a = Z_to_bv 64 pkl -> ew E b = Z_to_bv 64 fa -> (pkl = 0 \/ 128 <= pkl <= 135) -> 0 <= fa < 2 ^ 32 ->
bv_unsigned (sv_denot E (SAlu ALU_OR (SOff a 0) (SAlu ALU_SLL (SAlu ALU_AND (SOff b 0) (SLit 2)) (SLit 5)))) mod 2 ^ (8 * Z.of_N 1)
= pkl + (if YO07.flag fa 2 then 64 else 0).
Proof.
intros E a b pkl fa Ha Hb Hp Hf.
change (bv_unsigned (sv_denot E ?[e]) mod _ = _) with (U E (SAlu ALU_OR (SOff a 0) (SAlu ALU_SLL (SAlu ALU_AND (SOff b 0) (SLit 2)) (SLit 5))) mod 2 ^ (8 * Z.of_N 1) = pkl + (if YO07.flag fa 2 then 64 else 0)).
rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SLit. rewrite (U_atom E a pkl Ha ltac:(lia)), (U_atom E b fa Hb ltac:(lia)).
unfold zcanon, M64. change (2 mod 2 ^ 64) with 2. change (Z.land (5 mod 2 ^ 64) 63) with 5. change (2 ^ (8 * Z.of_N 1)) with 256.
destruct (land2_cases fa ltac:(lia)) as [Hl | Hl]; rewrite Hl.
- change ((0 mod 2 ^ 64) ≪ 5 mod 2 ^ 64) with 0. rewrite Z.lor_0_r. unfold YO07.flag. rewrite Hl. cbn [Z.eqb negb].
rewrite (Z.mod_small pkl) by lia. rewrite Z.mod_small by lia. lia.
- change ((2 mod 2 ^ 64) ≪ 5 mod 2 ^ 64) with 64. unfold YO07.flag. rewrite Hl. cbn [Z.eqb negb].
assert (Hc : pkl = 0 \/ pkl = 128 \/ pkl = 129 \/ pkl = 130 \/ pkl = 131 \/ pkl = 132 \/ pkl = 133 \/ pkl = 134 \/ pkl = 135) by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]; reflexivity.
Qed.
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section i.
Context {PI : PAImg lib_asan3_1_listing}.
Lemma rx_pkl_cases : forall cx : racx, c_slct cx <= 256 -> rx_pkl cx = 0 \/ 128 <= rx_pkl cx <= 135.
Proof.
intros cx Hs. unfold rx_pkl. destruct (Z.eqb_spec (c_slct cx) 0) as [Hz|Hnz]; cbn [negb]; [left; reflexivity | right].
pose proof (rx_pal_pow_range (c_slct cx) Hs). lia.
Qed.
End i.
End h.
Ltac xhdr10_facts HS :=
let AG := lazymatch goal with H : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => H end in
let LAWS := rnLAWS in let Bv := rnB in
let RF := lazymatch goal with H : ew _ 516 = Z_to_bv 64 _ |- _ => H end in
let HSINK := lazymatch goal with H : asink_at _ _ _ _ _ _ |- _ => H end in
let XF := lazymatch goal with H : xfacts (_ <= alloc_ceiling /\ 4096 <= _ /\ _) |- _ => H end in
let HSmax := lazymatch goal with H : xfacts (Z.of_nat (length _) + FRAME_OUT _ <= SINK_MAX) |- _ => H end in
let HXC := lazymatch goal with H : XC _ |- _ => H end in
let Rfattr := lazymatch goal with H : 0 <= ?fa < 2 ^ 32, E : ew _ 43 = Z_to_bv 64 ?fa |- _ => H end in
lazymatch type of RF with _ = Z_to_bv 64 ?Fv =>
lazymatch type of HSINK with asink_at _ _ _ _ ?pf ?SG =>
lazymatch goal with |- SRr _ _ _ (ra_postX _ _ _ _ ?cxv _) =>
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict ?Hw ?msx) =>
let rsm := eval vm_compute in (ss_mem ssx) in
let i0 := xidx_reg_off rsm 516%nat 48 in let r0 := eval vm_compute in (nth i0 rsm got_regionP) in
let i1 := xidx_reg_off rsm 516%nat 50 in let r1 := eval vm_compute in (nth i1 rsm got_regionP) in
let i2 := xidx_reg_off rsm 529%nat 6 in let r2 := eval vm_compute in (nth i2 rsm got_regionP) in
let HR0 := fresh "HR0" in let HR1 := fresh "HR1" in let HR2 := fresh "HR2" in
pose proof (st_ok_pi_region_nth Ev ssx (restrict Hw msx) i0 r0 HS ltac:(vm_compute; reflexivity)) as HR0; cbn [ms_mem restrict] in HR0;
pose proof (st_ok_pi_region_nth Ev ssx (restrict Hw msx) i1 r1 HS ltac:(vm_compute; reflexivity)) as HR1; cbn [ms_mem restrict] in HR1;
pose proof (st_ok_pi_region_nth Ev ssx (restrict Hw msx) i2 r2 HS ltac:(vm_compute; reflexivity)) as HR2; cbn [ms_mem restrict] in HR2;
let V48 := fresh "V48" in let V49 := fresh "V49" in let V50 := fresh "V50" in let V51 := fresh "V51" in let V52 := fresh "V52" in
let V53 := fresh "V53" in let V54 := fresh "V54" in let V55 := fresh "V55" in let V56 := fresh "V56" in let V57 := fresh "V57" in
xbyte HR0 48 V48; xbyte HR1 49 V49; xbyte HR1 50 V50; xbyte HR1 51 V51; xbyte HR1 52 V52; xbyte HR1 53 V53; xbyte HR1 54 V54;
xbyte HR1 55 V55; xbyte HR1 56 V56; xbyte HR1 57 V57;
let G661 := fresh "G661" in let G43 := fresh "G43" in let CX := fresh "CX" in let Hpk := fresh "Hpk" in let Hpkr := fresh "Hpkr" in
lazymatch type of V57 with val_mem _ _ _ _ (bv_unsigned (sv_denot ?Eo _) mod _) =>
xatom Eo 661%nat G661; xatom Eo 43%nat G43;
pose proof HXC as CX; unfold XC in CX; cbn [c_slct] in CX;
lazymatch type of G661 with _ = Z_to_bv 64 ?pk =>
assert (Hpk : pk = 0 \/ 128 <= pk <= 135) by (apply rx_pkl_cases; cbn [c_slct]; clear - CX; lia);
rewrite (xb_packed Eo 661 43 _ _ G661 G43 Hpk ltac:(clear - Rfattr; lia)) in V57;
lazymatch type of Rfattr with 0 <= ?fa < _ =>
assert (Hpkr : 0 <= pk + (if YO07.flag fa 2 then 64 else 0) < 256) by (destruct (YO07.flag fa 2); clear - Hpk; lia) end end;
clear G661 G43 CX end;
lazymatch type of HR0 with region_ok _ _ ?m _ =>
assert (HGA : garr8 pa_segs m (Fv + 48) (rx_hdr cxv))
by (unfold rx_hdr; cbn [c_left c_top c_w c_h YO07.u16le app]; unfold rx_packed; cbn [c_fattr]; xgarr8) end;
clear V48 V49 V50 V51 V52 V53 V54 V55 V56 V57 HR0 HR1 Hpk Hpkr;
let V6 := fresh "V6" in let V7 := fresh "V7" in let Hsh6 := fresh "Hsh6" in let Hsh7 := fresh "Hsh7" in let Hsa := fresh "Hsa" in
lazymatch type of HR2 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ev _ 529 (SB + Fv / 8) cs lo hi wlo whi 6 1%N (SLit 0) 0 HR2 ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V6;
pose proof (field_of_region Ev _ 529 (SB + Fv / 8) cs lo hi wlo whi 7 1%N (SLit 2) 2 HR2 ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V7 end;
clear HR2;
pose proof (aview_of_val_mem1 pa_segs _ _ _ _ V6 ltac:(lia)) as Hsh6; pose proof (aview_of_val_mem1 pa_segs _ _ _ _ V7 ltac:(lia)) as Hsh7;
let HFq := lazymatch goal with H : Fv = 32 * (Fv / 32) |- _ => H end in
let HF8 := lazymatch goal with H : Fv / 8 = 4 * (Fv / 32) |- _ => H end in
assert (Hsa : shadow_of_addr SHADOW_OFF (Fv + 48) = SB + Fv / 8 + 6)
by (unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF; rewrite HFq at 1; rewrite HF8;
replace (32 * (Fv / 32) + 48) with ((4 * (Fv / 32) + 6) * 8) by lia; rewrite Z.div_mul by lia; lia);
assert (HRAX : range_addressable (aview pa_segs Hw (ms_mem msx)) SHADOW_OFF (Fv + 48) 10)
by (apply (block_shadow_range _ _ (Fv + 48) 10); [| lia | lia];
apply block_shadow_cells2; [rewrite HFq; replace (32 * (Fv / 32) + 48) with ((4 * (Fv / 32) + 6) * 8) by lia; apply Z_mod_mult | lia
| rewrite Hsa; exact Hsh6 | rewrite Hsa; replace (SB + Fv / 8 + 6 + 1) with (SB + Fv / 8 + 7) by lia; exact Hsh7]);
clear V6 V7 Hsh6 Hsh7 Hsa;
let HJ3 := lazymatch goal with H : ajournal _ _ _ _ _ _ _ _ _ _ _ ?ly3 ?S3 _ (ms_mem msx) _ _ |- _ => H end in
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?ly3 ?S3 _ _ _ _ =>
let Hfin3 := lazymatch goal with H : In (1, ?fp) (frames S3) |- _ => H end in
let EFA3 := lazymatch goal with H : forall c p, frame_addr ly3 c p = frame_addr _ c p |- _ => H end in
lazymatch type of Hfin3 with In (1, ?fpos) _ =>
assert (HHVX : shadow_hull_vis (aview pa_segs Hw (ms_mem msx)) (Fv + 48) 10)
by (eapply (shadow_hull_vis_of_frame pa_segs Bv LAWS ly3 S3 _ _ _ 1 fpos (Fv + 48) 10 (proj1 HJ3) Hfin3);
[rewrite EFA3; lia | rewrite EFA3; change (fs_frame_bytes 1) with 128; lia | lia]) end end;
let HFhigh := lazymatch goal with H : in_app Fv 128 |- _ => H end in
let HFceil := lazymatch goal with H : Fv + 128 <= alloc_ceiling |- _ => H end in
let Lg := fresh "Lg" in
assert (HWX : 10 = Z.of_nat (length (rx_hdr cxv)) /\ 1 <= 10 <= 2 ^ 30 /\ Z.of_nat (length SG) + 10 <= SINK_MAX /\
(Fv + 48 + 10 <= pf \/ pf + FILE_BLOCK <= Fv + 48) /\ 0 <= Fv + 48 /\ amem_range (Fv + 48) 10)
by (split; [reflexivity|]; split; [lia|];
split; [ pose proof (rx_gce_length cxv) as Lg; rewrite ?length_app;
let Hw := match goal with H : 1 <= ?wv |- _ => lazymatch type of HSmax with context [FRAME_OUT (wv * _)] => H end end in
let Hh := match goal with H : 1 <= ?hv |- _ => lazymatch type of HSmax with context [FRAME_OUT (_ * hv)] => H end end in
clear - HSmax Hw Hh Lg; unfold xfacts in HSmax; unfold FRAME_OUT in HSmax; nia |];
split; [clear - XF; unfold xfacts in XF; unfold FILE_BLOCK; lia|]; split; [clear - XF; unfold xfacts in XF; lia|];
apply (amem_range_sub_app _ _ _ _ HFhigh HFceil); clear; lia)
end end end end.
Ltac xF8 :=
lazymatch goal with XF : xfacts (_ <= alloc_ceiling /\ 4096 <= _ /\ _), HF8 : ?Fv / 8 = 4 * (?Fv / 32), HFq : ?Fv = 32 * (?Fv / 32) |- _ =>
lazymatch type of XF with xfacts ?P =>
let XF2 := fresh "XF" in let XF1 := fresh "XF1" in
pose proof XF as XF1; unfold xfacts in XF1;
assert (XF2 : xfacts (Fv + 128 <= alloc_ceiling /\ 4096 <= Fv /\ (Fv = 8 * (Fv / 8) /\ P)))
by (apply xfacts_i; split; [clear - XF1; lia | split; [clear - XF1; lia | split; [clear - HF8 HFq; lia | exact XF1]]]);
clear XF XF1; rename XF2 into XF end end.
Ltac xW3 Wo :=
(repeat match goal with H : context [Wo] |- _ => first [clear H | fail 2 "xW3: the old world is still used in" H] end); try clear Wo;
lazymatch goal with |- SRr _ ?Wc _ _ => try rename Wc into Wo end.
Ltac xdummy_factsA HS :=
let AG := lazymatch goal with H : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => H end in
let RF := lazymatch goal with H : ew _ 516 = Z_to_bv 64 _ |- _ => H end in
lazymatch type of RF with _ = Z_to_bv 64 ?Fv =>
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict ?Hw ?msx) =>
let rsm := eval vm_compute in (ss_mem ssx) in
let i0 := xidx_reg_off rsm 516%nat 32 in let r0 := eval vm_compute in (nth i0 rsm got_regionP) in
let i2 := xidx_reg_off rsm 529%nat 4 in let r2 := eval vm_compute in (nth i2 rsm got_regionP) in
let HR0 := fresh "HR0" in let HR2 := fresh "HR2" in let V4 := fresh "V4" in let Hsh4 := fresh "Hsh4" in let Hsa := fresh "Hsa" in
let Vpd := fresh "Vpd" in let HRApd := fresh "HRApd" in
pose proof (st_ok_pi_region_nth Ev ssx (restrict Hw msx) i0 r0 HS ltac:(vm_compute; reflexivity)) as HR0; cbn [ms_mem restrict] in HR0;
pose proof (st_ok_pi_region_nth Ev ssx (restrict Hw msx) i2 r2 HS ltac:(vm_compute; reflexivity)) as HR2; cbn [ms_mem restrict] in HR2;
xbyte HR0 32 Vpd;
lazymatch type of HR2 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ev _ 529 (SB + Fv / 8) cs lo hi wlo whi 4 1%N (SLit 1) 1 HR2 ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V4 end;
pose proof (aview_of_val_mem1 pa_segs _ _ _ _ V4 ltac:(lia)) as Hsh4;
let HFq := lazymatch goal with H : Fv = 32 * (Fv / 32) |- _ => H end in
let HF8 := lazymatch goal with H : Fv / 8 = 4 * (Fv / 32) |- _ => H end in
assert (Hsa : shadow_of_addr SHADOW_OFF (Fv + 32) = SB + Fv / 8 + 4)
by (unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF; rewrite HFq at 1; rewrite HF8;
replace (32 * (Fv / 32) + 32) with ((4 * (Fv / 32) + 4) * 8) by lia; rewrite Z.div_mul by lia; lia);
assert (HRApd : range_addressable (aview pa_segs Hw (ms_mem msx)) SHADOW_OFF (Fv + 32) 1)
by (apply (block_shadow_range _ _ (Fv + 32) 1); [| lia | lia];
apply block_shadow_cells1; [rewrite HFq; replace (32 * (Fv / 32) + 32) with ((4 * (Fv / 32) + 4) * 8) by lia; apply Z_mod_mult | lia | rewrite Hsa; exact Hsh4]);
clear HR0 HR2 V4 Hsh4 Hsa end end.
Ltac xlct_facts Hlct Hc :=
let LAWS := rnLAWS in let Bv := rnB in
let HLCT := lazymatch goal with H : xfacts (0 < ?s <= 256 -> garr8 _ _ _ _ /\ _) |- _ => H end in
let HLCTsep := lazymatch goal with H : xfacts (0 < ?s <= 256 -> _ \/ _) |- _ => H end in
let HXC := lazymatch goal with H : XC _ |- _ => H end in
let HPerm := lazymatch goal with H : Permutation (ablocks _ ?ly ?S) ((?raw, RAW_SIZE) :: (?g, CGIF_SIZE) :: (?img, ?Ni) :: ?rest) |- _ => H end in
let HSINK := lazymatch goal with H : asink_at _ _ _ _ _ _ |- _ => H end in
let XF := lazymatch goal with H : xfacts (_ <= alloc_ceiling /\ 4096 <= _ /\ _) |- _ => H end in
let HSmax := lazymatch goal with H : xfacts (Z.of_nat (length _) + FRAME_OUT _ <= SINK_MAX) |- _ => H end in
let HS := lazymatch goal with H : st_ok_pi _ _ _ _ _ |- _ => H end in
let E49 := lazymatch goal with H : ew _ 49 = Z_to_bv 64 _ |- _ => H end in
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict ?Hw ?msx) =>
let HJ3 := lazymatch goal with H : ajournal _ _ _ _ _ _ _ _ _ _ _ ?ly3 ?S3 _ (ms_mem msx) _ _ |- _ => H end in
lazymatch type of HJ3 with ajournal _ _ _ _ ?FP ?ly ?S ?W ?mem ?md _ ?ly3 ?S3 ?W3 _ _ _ =>
lazymatch type of HPerm with Permutation _ ((?raw, RAW_SIZE) :: (?g, CGIF_SIZE) :: (?img, ?Ni) :: ?rest) =>
lazymatch type of HSINK with asink_at _ _ _ _ ?pf ?SG =>
lazymatch type of Hc with ?slct <> 0 =>
let HAR := lazymatch goal with H : AR _ _ ly S W mem md |- _ => H end in
let HPerm3 := lazymatch goal with H : Permutation (ablocks _ ly3 S3) _ |- _ => H end in
let Nl := fresh "Nl" in let rest' := fresh "rest'" in let HPl := fresh "HPl" in let HNl := fresh "HNl" in let HLl := fresh "HLl" in
let HGL0 := fresh "HGL0" in let HLlen := fresh "HLlen" in let Hlin := fresh "Hlct_in" in let Hlin3 := fresh "Hlct3" in let Srl := fresh "Srl" in
let Hsep := fresh "Hlsep" in let CX := fresh "CX" in let Hs := fresh "Hslct" in let Hq := fresh "Hq" in let Lq := fresh "Lq" in
let Hl4096 := fresh "Hl4096" in let Hlceil := fresh "Hlceil" in
pose proof HXC as CX; unfold XC in CX; cbn [c_slct] in CX;
assert (Hs : 0 < slct <= 256) by (lazymatch goal with R : 0 <= slct < _ |- _ => clear - Hc CX R; lia end); clear CX;
destruct (Hlct Hs) as (Nl & rest' & HPl & HNl);
pose proof HLCT as HLl; unfold xfacts in HLl; destruct (HLl Hs) as [HGL0 HLlen]; clear HLl;
pose proof HLCTsep as Hsep; unfold xfacts in Hsep; specialize (Hsep Hs);
lazymatch type of HGL0 with garr8 _ _ ?lct ?LCT =>
assert (Hlin : In (lct, Nl) (ablocks Bv ly S))
by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; right; right; right; eapply Permutation_in; [apply Permutation_sym; exact HPl|]; left; reflexivity);
assert (Hlin3 : In (lct, Nl) (ablocks Bv ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; right; exact Hlin);
pose proof (sep_blocks_perm _ Bv LAWS ly S W mem md (raw, RAW_SIZE) (lct, Nl) ((g, CGIF_SIZE) :: (img, Ni) :: rest') HAR
ltac:(eapply Permutation_trans; [exact HPerm|]; apply perm_skip;
eapply Permutation_trans; [apply perm_skip; apply perm_skip; exact HPl|];
eapply Permutation_trans; [apply perm_skip; apply perm_swap|]; apply perm_swap)) as Srl;
unfold zdisjoint, block_rng in Srl; cbn [fst snd] in Srl; change (req_size RAW_SIZE) with 48 in Srl;
pose proof (req_size_pos Nl ltac:(clear - HNl Hs; lia)) as [_ Hq];
destruct (al_blocks _ _ LAWS _ _ _ _ _ lct Nl (proj1 HJ3) Hlin3) as (_ & Hl4096 & Hlceil & _ & _ & _);
assert (Lq : Z.of_nat (length (firstn (Z.to_nat (slct * 3)) LCT)) = slct * 3) by (rewrite length_firstn, Nat2Z.inj_min, Z2Nat.id by (clear - Hs; lia); clear - HLlen Hs; lia);
assert (HGA : garr8 pa_segs (mrestrict (w_H W3) (ms_mem msx)) lct (firstn (Z.to_nat (slct * 3)) LCT));
[ eapply (garr8_journal_block_x _ Bv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lct Nl lct _ HJ3);
[ exact Hlin | exact Hlin3 | clear; lia | rewrite Lq; clear - HNl Hq; lia
| let a := fresh "a" in let Ha := fresh "Ha" in let r := fresh "r" in let Hr1 := fresh "Hr1" in let Hr2 := fresh "Hr2" in let HrF := fresh "HrF" in
rewrite Lq; intros a Ha (r & [<- | Hr1] & Hr2);
[ cbn [fst snd] in Hr2; clear - Ha Hr2 Srl HNl Hq Hs; lia
| pose proof (proj1 (in_asink_fp pf a) (ex_intro _ r (conj Hr1 Hr2))) as HrF; clear - Ha HrF Hsep Hl4096 Hs; unfold FILE_BLOCK in *; lia ]
| let HG1 := fresh "HG1" in
pose proof (garr8_sub_x pa_segs _ lct LCT 0 (Z.to_nat (slct * 3)) HGL0 ltac:(rewrite Nat.add_0_l; apply Nat2Z.inj_le; rewrite Z2Nat.id by (clear - Hs; lia); clear - HLlen Hs; lia)) as HG1;
rewrite skipn_O, Z.add_0_r in HG1; exact HG1 ]
| ];
assert (HRAX : range_addressable (aview pa_segs Hw (ms_mem msx)) SHADOW_OFF lct (slct * 3))
by (apply (range_addressable_of_block _ Bv LAWS _ _ _ _ _ lct Nl lct (slct * 3) (proj1 HJ3) Hlin3); clear - HNl Hq Hs; lia);
assert (HHVX : shadow_hull_vis (aview pa_segs Hw (ms_mem msx)) lct (slct * 3))
by (apply (shadow_hull_vis_of_block _ Bv LAWS _ _ _ _ _ lct Nl lct (slct * 3) (proj1 HJ3) Hlin3); clear - HNl Hq Hs; lia);
assert (HWX : slct * 3 = Z.of_nat (length (firstn (Z.to_nat (slct * 3)) LCT)) /\ 1 <= slct * 3 <= 2 ^ 30 /\ Z.of_nat (length SG) + slct * 3 <= SINK_MAX /\
(lct + slct * 3 <= pf \/ pf + FILE_BLOCK <= lct) /\ 0 <= lct /\ amem_range lct (slct * 3))
by (split; [rewrite Lq; reflexivity|]; split; [clear - Hs; lia|];
split; [ let Lg := fresh "Lg" in let Lh := fresh "Lh" in
lazymatch SG with context [rx_gce ?cxv] => pose proof (rx_gce_length cxv) as Lg; pose proof (rx_hdr_length cxv) as Lh end;
rewrite ?length_app;
let Hw := match goal with H : 1 <= ?wv |- _ => lazymatch type of HSmax with context [FRAME_OUT (wv * _)] => H end end in
let Hh := match goal with H : 1 <= ?hv |- _ => lazymatch type of HSmax with context [FRAME_OUT (_ * hv)] => H end end in
clear - HSmax Hw Hh Lg Lh Hs; unfold xfacts in HSmax; unfold FRAME_OUT in HSmax; nia |];
split; [clear - Hsep Hs; lia|]; split; [clear - Hl4096; lia|];
apply (amem_range_of_block _ Bv LAWS _ _ _ _ _ lct Nl lct (slct * 3) (proj1 HJ3) Hlin3); clear - HNl Hq Hs; lia);
let XF2 := fresh "XF" in
lazymatch type of XF with xfacts ?P =>
assert (XF2 : xfacts (lct + slct * 3 <= alloc_ceiling /\ 4096 <= lct /\ P))
by (apply xfacts_i; split; [clear - Hlceil HNl Hq Hs; lia | split; [exact Hl4096 | let XF1 := fresh "XF1" in pose proof XF as XF1; unfold xfacts in XF1; exact XF1]]);
clear XF; rename XF2 into XF end;
lazymatch type of E49 with ew ?Eb 49 = _ =>
assert (XA2 : sv_denot Eb (SMd M_MUL (SOff 49 0) (SLit 3)) = w64 (slct * 3)) by (apply (denot_mul3 Eb 49 slct); [exact E49 | clear - Hs; lia]);
cbn [sv_denot] in XA2; rewrite Z.add_0_r, Z_to_bv_bv_unsigned in XA2 end;
clear Hq Lq HPl Srl Hsep
end end end end end end.
