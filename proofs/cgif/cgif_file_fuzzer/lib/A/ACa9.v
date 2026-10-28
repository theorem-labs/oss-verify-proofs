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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACb6 ACba AC9z ACa3 ACa4 ACa5 ACa6 ACa7 ACa8.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma xb_icl : forall E a v, ew E a = Z_to_bv 64 v -> 1 <= v < 256 ->
bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff a 0) (SLit 255)) (SLit (-1)))) mod 2 ^ (8 * Z.of_N 1) = v - 1.
Proof.
intros E a v Ha Hv.
change (bv_unsigned (sv_denot E ?[e]) mod _ = _) with (U E (SAlu ALU_ADD (SAlu ALU_AND (SOff a 0) (SLit 255)) (SLit (-1))) mod 2 ^ (8 * Z.of_N 1) = v - 1).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E a v Ha ltac:(lia)), !U_SLit.
unfold zcanon, M64. change (255 mod 2 ^ 64) with 255. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1). change (2 ^ (8 * Z.of_N 1)) with 256.
replace (Z.land v 255) with v by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
rewrite (Z.mod_small v) by lia.
replace (v + (2 ^ 64 - 1)) with ((v - 1) + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full. rewrite (Z.mod_small (v - 1)) by lia. apply Z.mod_small. lia.
Qed.
Lemma xb_icl_b : forall E a v, ew E a = Z_to_bv 64 v -> 1 <= v < 256 ->
bv_unsigned (sv_denot E (SOff a (-1))) mod 2 ^ (8 * Z.of_N 1) = v - 1.
Proof.
intros E a v Ha Hv. cbn [sv_denot]. rewrite Ha. rewrite (unsigned_lit_small v) by lia. rewrite unsigned_lit_small by lia.
change (2 ^ (8 * Z.of_N 1)) with 256. rewrite Z.mod_small by lia. lia.
Qed.
Ltac xicl_facts HS :=
let AG := lazymatch goal with H : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => H end in
let LAWS := rnLAWS in let Bv := rnB in
let RF := lazymatch goal with H : ew _ 516 = Z_to_bv 64 _ |- _ => H end in
let HSINK := lazymatch goal with H : asink_at _ _ _ _ _ _ |- _ => H end in
let XF := lazymatch goal with H : xfacts (_ <= alloc_ceiling /\ 4096 <= _ /\ _) |- _ => H end in
let HSmax := lazymatch goal with H : xfacts (Z.of_nat (length _) + FRAME_OUT _ <= SINK_MAX) |- _ => H end in
let HXC := lazymatch goal with H : XC _ |- _ => H end in
let EICL := lazymatch goal with H : ew _ 759 = Z_to_bv 64 (rx_iclen _) |- _ => H end in
lazymatch type of RF with _ = Z_to_bv 64 ?Fv =>
lazymatch type of HSINK with asink_at _ _ _ _ ?pf ?SG =>
lazymatch goal with |- SRr _ _ _ (ra_postX _ _ _ _ ?cxv _) =>
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict ?Hw ?msx) =>
let rsm := eval vm_compute in (ss_mem ssx) in
let i0 := xidx_reg_off rsm 516%nat 112 in let r0 := eval vm_compute in (nth i0 rsm got_regionP) in
let i2 := xidx_reg_off rsm 529%nat 14 in let r2 := eval vm_compute in (nth i2 rsm got_regionP) in
let HR0 := fresh "HR0" in let HR2 := fresh "HR2" in let V112 := fresh "V112" in
pose proof (st_ok_pi_region_nth Ev ssx (restrict Hw msx) i0 r0 HS ltac:(vm_compute; reflexivity)) as HR0; cbn [ms_mem restrict] in HR0;
pose proof (st_ok_pi_region_nth Ev ssx (restrict Hw msx) i2 r2 HS ltac:(vm_compute; reflexivity)) as HR2; cbn [ms_mem restrict] in HR2;
lazymatch type of HR0 with region_ok _ _ ?m (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch cs with context [YP09.mkChunk 112 (CVal 1 ?e)] =>
pose proof (field_of_region_any Ev m 516 Fv cs lo hi wlo whi 112 1%N e HR0 ltac:(evalE AG) ltac:(cbn; tauto) ltac:(cbn; lia)) as V112;
change (N.to_nat 1) with 1%nat in V112;
let E759 := fresh "E759" in xatom Ev 759%nat E759;
first [ rewrite (xb_icl Ev 759 (rx_iclen cxv) E759 ltac:(pose proof (rx_iclen_bounds cxv); lia)) in V112
| rewrite (xb_icl_b Ev 759 (rx_iclen cxv) E759 ltac:(pose proof (rx_iclen_bounds cxv); lia)) in V112 ]; clear E759 end end;
let Hiclr := fresh "Hiclr" in
assert (Hiclr : 0 <= rx_iclen cxv - 1 < 256) by (pose proof (rx_iclen_bounds cxv); lia);
lazymatch type of HR0 with region_ok _ _ ?m _ =>
assert (HGA : garr8 pa_segs m (Fv + 112) [rx_iclen cxv - 1]) by xgarr8 end;
clear V112 HR0 Hiclr;
let V14 := fresh "V14" in let Hsh14 := fresh "Hsh14" in let Hsa := fresh "Hsa" in
lazymatch type of HR2 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ev _ 529 (SB + Fv / 8) cs lo hi wlo whi 14 1%N (SLit 1) 1 HR2 ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V14 end;
clear HR2;
pose proof (aview_of_val_mem1 pa_segs _ _ _ _ V14 ltac:(lia)) as Hsh14;
let HFq := lazymatch goal with H : Fv = 32 * (Fv / 32) |- _ => H end in
let HF8 := lazymatch goal with H : Fv / 8 = 4 * (Fv / 32) |- _ => H end in
assert (Hsa : shadow_of_addr SHADOW_OFF (Fv + 112) = SB + Fv / 8 + 14)
by (unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF; rewrite HFq at 1; rewrite HF8;
replace (32 * (Fv / 32) + 112) with ((4 * (Fv / 32) + 14) * 8) by lia; rewrite Z.div_mul by lia; lia);
assert (HRAX : range_addressable (aview pa_segs Hw (ms_mem msx)) SHADOW_OFF (Fv + 112) 1)
by (apply (block_shadow_range _ _ (Fv + 112) 1); [| lia | lia];
apply block_shadow_cells1; [rewrite HFq; replace (32 * (Fv / 32) + 112) with ((4 * (Fv / 32) + 14) * 8) by lia; apply Z_mod_mult | lia | rewrite Hsa; exact Hsh14]);
clear V14 Hsh14 Hsa;
let HJ3 := lazymatch goal with H : ajournal _ _ _ _ _ _ _ _ _ _ _ ?ly3 ?S3 _ (ms_mem msx) _ _ |- _ => H end in
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?ly3 ?S3 _ _ _ _ =>
let Hfin3 := lazymatch goal with H : In (1, ?fp) (frames S3) |- _ => H end in
let EFA3 := lazymatch goal with H : forall c p, frame_addr ly3 c p = frame_addr _ c p |- _ => H end in
lazymatch type of Hfin3 with In (1, ?fpos) _ =>
assert (HHVX : shadow_hull_vis (aview pa_segs Hw (ms_mem msx)) (Fv + 112) 1)
by (eapply (shadow_hull_vis_of_frame pa_segs Bv LAWS ly3 S3 _ _ _ 1 fpos (Fv + 112) 1 (proj1 HJ3) Hfin3);
[rewrite EFA3; lia | rewrite EFA3; change (fs_frame_bytes 1) with 128; lia | lia]) end end;
let HFhigh := lazymatch goal with H : in_app Fv 128 |- _ => H end in
let HFceil := lazymatch goal with H : Fv + 128 <= alloc_ceiling |- _ => H end in
let Lg := fresh "Lg" in let Lh := fresh "Lh" in let Ll := fresh "Ll" in let CX := fresh "CX" in
assert (HWX : 1 = Z.of_nat (length [rx_iclen cxv - 1]) /\ 1 <= 1 <= 2 ^ 30 /\ Z.of_nat (length SG) + 1 <= SINK_MAX /\
(Fv + 112 + 1 <= pf \/ pf + FILE_BLOCK <= Fv + 112) /\ 0 <= Fv + 112 /\ amem_range (Fv + 112) 1)
by (split; [reflexivity|]; split; [lia|];
split; [ pose proof (rx_gce_length cxv) as Lg; pose proof (rx_hdr_length cxv) as Lh;
pose proof HXC as CX; unfold XC in CX;
lazymatch SG with context [rx_lctb _ ?LCTv] => pose proof (rx_lctb_length cxv LCTv (proj2 CX)) as Ll end;
rewrite ?length_app;
let Hw := match goal with H : 1 <= ?wv |- _ => lazymatch type of HSmax with context [FRAME_OUT (wv * _)] => H end end in
let Hh := match goal with H : 1 <= ?hv |- _ => lazymatch type of HSmax with context [FRAME_OUT (_ * hv)] => H end end in
clear - HSmax Hw Hh Lg Lh Ll; unfold xfacts in HSmax; unfold FRAME_OUT in HSmax; nia |];
split; [clear - XF; unfold xfacts in XF; unfold FILE_BLOCK; lia|]; split; [clear - XF; unfold xfacts in XF; lia|];
apply (amem_range_sub_app _ _ _ _ HFhigh HFceil); clear; lia)
end end end end.
Lemma xze32 : forall E a M, ew E a = Z_to_bv 64 (M mod 2 ^ 32) -> 0 <= M < 2 ^ 32 -> zext 64 (bv_extract 0 32 (ew E a)) = Z_to_bv 64 M.
Proof.
intros E a M Ha HM. rewrite Ha, zext64_lit, bv_extract_0_unsigned, Z_to_bv_unsigned. f_equal.
change (bv_wrap 32 (bv_wrap 64 (M mod 2 ^ 32))) with ((M mod 2 ^ 32) mod 2 ^ 64 mod 2 ^ 32).
rewrite (Z.mod_small M) by lia. rewrite (Z.mod_small M) by lia. apply Z.mod_small. lia.
Qed.
Ltac xras_facts :=
let LAWS := rnLAWS in let Bv := rnB in
let HSINK := lazymatch goal with H : asink_at _ _ _ _ _ _ |- _ => H end in
let XF := lazymatch goal with H : xfacts (_ <= alloc_ceiling /\ 4096 <= _ /\ _) |- _ => H end in
let HSmax := lazymatch goal with H : xfacts (Z.of_nat (length _) + FRAME_OUT _ <= SINK_MAX) |- _ => H end in
let HXC := lazymatch goal with H : XC _ |- _ => H end in
let XBB := lazymatch goal with H : xbfacts (4096 <= ?bb /\ _) |- _ => H end in
lazymatch type of XBB with xbfacts (4096 <= ?bb /\ _) =>
let HGout := lazymatch goal with H : garr8 _ _ bb ?out |- _ => H end in
lazymatch type of HGout with garr8 _ (mrestrict ?Hw (ms_mem ?msx)) bb ?out =>
let HMo := lazymatch goal with H : ?M = Z.of_nat (length out) |- _ => H end in
lazymatch type of HMo with ?M = _ =>
let HM := lazymatch goal with H : 1 <= M <= ?Lbb |- _ => H end in
lazymatch type of HM with 1 <= M <= ?Lbb =>
let HML := lazymatch goal with H : xfacts (Z.of_nat (length out) <= req_size Lbb) |- _ => H end in
let HM16 := lazymatch goal with H : Z.of_nat (length out) <= 2 * _ + 16 |- _ => H end in
let HLbbmax := lazymatch goal with H : 0 <= Lbb < MALLOC_MAX |- _ => H end in
let E1060 := lazymatch goal with H : ew _ 1060 = Z_to_bv 64 (M mod 2 ^ 32) |- _ => H end in
let HJ3 := lazymatch goal with H : ajournal _ _ _ _ _ _ _ _ _ _ _ ?ly3 ?S3 _ (ms_mem msx) _ _ |- _ => H end in
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?ly3 ?S3 _ _ _ _ =>
let Hbb3 := lazymatch goal with H : In (bb, Lbb) (ablocks _ ly3 S3) |- _ => H end in
lazymatch type of HSINK with asink_at _ _ _ _ ?pf ?SG =>
lazymatch goal with |- SRr _ _ _ (ra_postX _ _ _ _ ?cxv _) =>
let HMLu := fresh "HMLu" in let XBu := fresh "XBu" in
pose proof HML as HMLu; unfold xfacts in HMLu; pose proof XBB as XBu; unfold xbfacts in XBu;
pose proof HGout as HGA;
assert (HRAX : range_addressable (aview pa_segs Hw (ms_mem msx)) SHADOW_OFF bb M)
by (apply (range_addressable_of_block _ Bv LAWS _ _ _ _ _ bb Lbb bb M (proj1 HJ3) Hbb3); clear - HM HMo HMLu; lia);
assert (HHVX : shadow_hull_vis (aview pa_segs Hw (ms_mem msx)) bb M)
by (apply (shadow_hull_vis_of_block _ Bv LAWS _ _ _ _ _ bb Lbb bb M (proj1 HJ3) Hbb3); clear - HM HMo HMLu; lia);
let XF2 := fresh "XF" in
lazymatch type of XF with xfacts ?P =>
assert (XF2 : xfacts (bb + M <= alloc_ceiling /\ 4096 <= bb /\ P))
by (apply xfacts_i; split; [clear - HM HMo HMLu XBu; lia | split; [clear - XBu; lia | let XF1 := fresh "XF1" in pose proof XF as XF1; unfold xfacts in XF1; exact XF1]]);
clear XF; rename XF2 into XF end;
let Lg := fresh "Lg" in let Lh := fresh "Lh" in let Ll := fresh "Ll" in let CX := fresh "CX" in
assert (HWX : M = Z.of_nat (length out) /\ 1 <= M <= 2 ^ 30 /\ Z.of_nat (length SG) + M <= SINK_MAX /\
(bb + M <= pf \/ pf + FILE_BLOCK <= bb) /\ 0 <= bb /\ amem_range bb M)
by (split; [exact HMo|]; split; [clear - HM HLbbmax; unfold MALLOC_MAX in HLbbmax; lia|];
split; [ pose proof (rx_gce_length cxv) as Lg; pose proof (rx_hdr_length cxv) as Lh;
pose proof HXC as CX; unfold XC in CX;
lazymatch SG with context [rx_lctb _ ?LCTv] => pose proof (rx_lctb_length cxv LCTv (proj2 CX)) as Ll end;
rewrite ?length_app; cbn [length];
let Hw := match goal with H : 1 <= ?wv |- _ => lazymatch type of HSmax with context [FRAME_OUT (wv * _)] => H end end in
let Hh := match goal with H : 1 <= ?hv |- _ => lazymatch type of HSmax with context [FRAME_OUT (_ * hv)] => H end end in
clear - HSmax Hw Hh Lg Lh Ll HM16 HMo; unfold xfacts in HSmax; unfold FRAME_OUT in HSmax; nia |];
split; [clear - XBu HM HMo HMLu; unfold FILE_BLOCK; lia|]; split; [clear - XBu; lia|];
apply (amem_range_of_block _ Bv LAWS _ _ _ _ _ bb Lbb bb M (proj1 HJ3) Hbb3); clear - HM HMo HMLu; lia);
lazymatch type of E1060 with ew ?Eb 1060 = _ =>
assert (XA2 : zext 64 (bv_extract 0 32 (ew Eb 1060)) = Z_to_bv 64 M) by (apply (xze32 Eb 1060%nat M E1060); clear - HM HLbbmax; unfold MALLOC_MAX in HLbbmax; lia) end;
clear HMLu XBu
end end end end end end end.
