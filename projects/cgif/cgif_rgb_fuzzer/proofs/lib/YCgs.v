(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI03 YI04 YI1i YI20.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCfu YCe9 YCe1 YCe4 YCgu YCgv.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma awr_byte_callee0 : forall STK STK' sp sp' (bl0 bl0' blc : list (Z * Z)) lyq lyq' a,
awr_byte STK' sp' [] bl0' blc lyq' [] a -> sp - STK <= sp' - STK' -> sp' <= sp -> (forall b, In b bl0 -> In b bl0') ->
awr_byte STK sp [] bl0 blc lyq [] a.
Proof.
intros STK STK' sp sp' bl0 bl0' blc lyq lyq' a [H | [[Hf _] | [(b & n & Hin & Hn0 & Hb) | (c & p & Hin & _)]]] H1 H2 Hsub.
- left. lia.
- exfalso. exact (inFP_nil _ Hf).
- right; right; left. exists b, n. split; [exact Hin|]. split; [intros Hc; exact (Hn0 (Hsub _ Hc)) | exact Hb].
- destruct Hin.
Qed.
Section h.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes trbsegs B.
Hypothesis AFREE : afree_realizes trbsegs B.
Hypothesis AMEMSET : aintrin_realizes trbsegs B OSet A_asan_memset.
Hypothesis AMEMCPY : aintrin_realizes trbsegs B OCpy A_asan_memcpy.
Hypothesis ASF : astack_free_law trbsegs B.
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis RAWNEW : trawnew_spec B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.
Local Notation code := (as_code B).
Lemma ng_P0 : NG_P0_stmt B.
Proof.
intros ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops rest cid pos E0 E W3 ly3 S3 ms3 md3 k fpos g HCTX HCFG HE0 HE Rg HNOW HW0 HH0 Ha4 HS.
ng_facts HCTX HCFG HE0 HE.
destruct HNOW as (HJ3 & Hk3 & Hfrs3 & Eab3 & Hg4096 & Tg & Ag).
ng_frame HJ3 Hfrs3.
assert (Hg_in : In (g, 96) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ g 96 HAR3 Hg_in) as (Hg16 & _ & Hgceil & Hgh_ia & Hgpres3 & _). pose proof (proj1 Hgh_ia) as Hgh. change (req_size 96) with 96 in Hgceil, Hgpres3.
pose proof (blk_off_img _ _ _ _ _ _ g 96 HAR3 Hg_in) as Hgh_img.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ g 96 1 fpos HAR3 Hg_in Hfin3) as HdGF.
unfold zdisjoint in HdGF. cbn [fst snd] in HdGF. change (req_size 96) with 96 in HdGF. change (fs_frame_bytes 1) with 128 in HdGF. rewrite EFA3 in HdGF. fold F in HdGF.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ g 96 cid pos HAR3 Hg_in HfinS3) as HdGC.
unfold zdisjoint in HdGC. cbn [fst snd] in HdGC. change (req_size 96) with 96 in HdGC. rewrite EFA3 in HdGC.
nbox_seps.
aconsts HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
assert (E10' : ew E 10 = Z_to_bv 64 cfgp) by (rewrite (AG 10%nat) by lia; exact E10).
reshok_bx HS 35%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK NBspan A_cgif_raw_newgif.
all: try (slim; oblF HJ3 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: try (slim; awrR AG fpos F EFA3).
clear_frames.
set (sgct := 0).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 45%nat in let i := eval vm_compute in i in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i _ HS eq_refl) as HRc; cbn [ms_mem restrict] in HRc;
lazymatch type of HRc with region_ok _ _ _ (YQ0b.mkRegion (Some 45%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 45 F cs lo hi wlo whi 32 8%N (SLit 549568) A_cgif_writecb HRc
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia)
ltac:(cbn; tauto) ltac:(reflexivity) ltac:(unfold A_cgif_writecb; zside) ltac:(cbn; lia)) as Vwfn;
pose proof (field_of_region Ex _ 45 F cs lo hi wlo whi 40 8%N (SOff 79 0) g HRc
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia)
ltac:(cbn; tauto) ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Rg, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; clear - Hg4096 Hgceil C1; lia) ltac:(cbn; lia)) as Vctx;
pose proof (field_of_region Ex _ 45 F cs lo hi wlo whi 48 8%N (SOff 32 0) pal0 HRc
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia)
ltac:(cbn; tauto) ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 32%nat) by lia; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; clear - CR0; lia) ltac:(cbn; lia)) as Vgct;
pose proof (field_of_region Ex _ 45 F cs lo hi wlo whi 56 4%N _ (ng_rattr attr) HRc
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia)
ltac:(cbn; tauto)
ltac:(rewrite denot_lit_U; f_equal; apply (U_ng_rattr _ 33 attr); [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E33 | exact CR16])
ltac:(pose proof (ng_rattr_range attr ltac:(clear - CR16; lia)); cbn; lia) ltac:(cbn; lia)) as Vrat;
let gh off e n v Hn Rv V := pose proof (field_of_region_any Ex _ 45 F cs lo hi wlo whi off 2%N e HRc
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia)
ltac:(cbn; tauto) ltac:(cbn; lia)) as V;
change (bv_unsigned (sv_denot Ex e)) with (U Ex e) in V; change (2 ^ (8 * Z.of_N 2)) with (2 ^ 16) in V;
rewrite (U_sext16_mod Ex (SOff n 0) v ltac:(apply (U_atom Ex n v); [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact Hn | clear - Rv; lia]) Rv) in V in
gh 60 (SExt true 16 (SOff 36 0)) 36%nat Wd E36 CR24 VW;
gh 62 (SExt true 16 (SOff 37 0)) 37%nat Hd E37 CR26 VH;
gh 66 (SExt true 16 (SOff 39 0)) 39%nat loops E39 CR30 Vlp
end; clear HRc end.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 45%nat in let i := eval vm_compute in i in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i _ HS eq_refl) as HRc; cbn [ms_mem restrict] in HRc;
lazymatch type of HRc with region_ok _ _ _ (YQ0b.mkRegion (Some 45%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 45 F cs lo hi wlo whi 64 2%N (SLit 0) 0 HRc
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia)
ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vsg end; clear HRc end.
cbn [N.to_nat] in Vwfn, Vctx, Vgct, Vrat, VW, VH, Vlp, Vsg.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (Ocfg : obj_at trbsegs (mrestrict (w_H W3) (ms_mem msX)) (F + 32) LAY_RawConfig [A_cgif_writecb; g; pal0; ng_rattr attr; Wd; Hd; sgct; loops]) end.
{ cbn [obj_at LAY_RawConfig]. unfold field_ok. cbn [fst snd N.to_nat Z.of_N].
pose proof (ng_rattr_range attr ltac:(clear - CR16; lia)) as Hrr.
replace (F + 32 + 0) with (F + 32) by lia. replace (F + 32 + 8) with (F + 40) by lia. replace (F + 32 + 16) with (F + 48) by lia.
replace (F + 32 + 24) with (F + 56) by lia. replace (F + 32 + 28) with (F + 60) by lia. replace (F + 32 + 30) with (F + 62) by lia.
replace (F + 32 + 32) with (F + 64) by lia. replace (F + 32 + 34) with (F + 66) by lia.
repeat split; try assumption; clear - Hrr CR0 CR16 CR24 CR26 CR28 CR30 Hg4096 Hgceil C1 sgct; cbv delta [sgct]; unfold A_cgif_writecb; lia. }
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 79%nat in let i := eval vm_compute in i in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i _ HS eq_refl) as HRg; cbn [ms_mem restrict] in HRg;
assert (HB79 : bv_unsigned (ew Ex 79) = g) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Rg; apply unsigned_lit_small; clear - Hg4096 Hgceil C1; lia);
lazymatch type of HRg with region_ok _ _ _ (YQ0b.mkRegion (Some 79%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 79 g cs lo hi wlo whi 56 8%N (SLit A_writecb) A_writecb HRg HB79 ltac:(cbn; tauto) eq_refl ltac:(unfold A_writecb; zside) ltac:(cbn; lia)) as Gwfn;
pose proof (field_of_region Ex _ 79 g cs lo hi wlo whi 64 8%N (SLit 0) 0 HRg HB79 ltac:(cbn; tauto) eq_refl ltac:(zside) ltac:(cbn; lia)) as Gctx;
pose proof (field_of_region Ex _ 79 g cs lo hi wlo whi 80 8%N (SLit 0) 0 HRg HB79 ltac:(cbn; tauto) eq_refl ltac:(zside) ltac:(cbn; lia)) as Gfile
end; clear HRg end.
cbn [N.to_nat] in Gwfn, Gctx, Gfile.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 58%nat in let i := eval vm_compute in i in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i _ HS eq_refl) as HRfs; cbn [ms_mem restrict] in HRfs;
lazymatch type of HRfs with region_ok _ _ _ (YQ0b.mkRegion (Some 58%nat) ?lo ?hi ?wlo ?whi ?cs) =>
assert (ZS5 : forall j, 4 <= j <= 8 -> val_mem trbsegs (mrestrict (w_H W3) (ms_mem msX)) (SB + F / 8 + j) 1 0);
[ let j := fresh "j" in let Hj := fresh "Hj" in let Hj5 := fresh "Hj5" in intros j Hj;
assert (Hj5 : j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8) by (clear - Hj; lia);
destruct Hj5 as [-> | [-> | [-> | [-> | ->]]]];
(eapply (field_of_region Ex _ 58 (SB + F / 8) cs lo hi wlo whi _ 1%N (SLit 0) 0 HRfs);
[evalE AG | cbn; tauto | reflexivity | cbn; lia | cbn; lia])
| ] end;
clear HRfs;
assert (HRA40 : range_addressable (aview trbsegs (w_H W3) (ms_mem msX)) SHADOW_OFF (F + 32) 40);
[ apply zero_shadow_range; [rewrite HFq; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by lia; apply Z_mod_mult | reflexivity |];
let ii := fresh "ii" in let Hii := fresh "Hii" in
intros ii Hii; change (40 / 8) with 5 in Hii; unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF;
replace (SB + (F + 32) / 8 + ii) with (SB + F / 8 + (4 + ii)) by (rewrite HFq at 2; rewrite HF8; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by lia; rewrite Z.div_mul by lia; lia);
apply (aview_of_val_mem1 trbsegs); [apply ZS5; clear - Hii; lia | clear; lia]
| ] end.
assert (HEVc : vev S3 + EV_RAWNEW <= VEV_MAX).
{ pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _). unfold EV_RAWNEW. rewrite HEV in Hev. clear - Hnev3 Hk3 Hev. lia. }
assert (HLIVEc : blocks_bytes S3 + 2 ^ 16 <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly3 S3), Eab3, !bsum_app, <- (blocks_bytes_bsum B ly S). cbn [bsum fold_right snd]. unfold LIVE_NEWGIF in Hlive. clear - Hlive CR28. lia. }
pose (restX := ablocks B ly S).
assert (HBL : Permutation (ablocks B ly3 S3) ((g, CGIF_SIZE) :: restX)).
{ subst restX. rewrite Eab3. apply Permutation_sym. apply Permutation_cons_append. }
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3. aconsts HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp.
rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
ng_chain HS HJ3 AG EE.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (HspX : spZ (ms_regs msX) = spZ regs - 192) by (unfold spZ at 1; rewrite Rsp; evalE AG; clear; lia) end.
pose proof (proj1 (proj2 HJ3)) as HLY3. pose proof HLY3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop3 & _).
lazymatch type of HS with st_ok _ ?Ex ?ssX (restrict _ ?msX) =>
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdX) _ =>
eapply SRr_bind;
[ eapply (aj_call trbsegs B LAWS trb_segs_low W3 Ex ssX msX TNEWGIF_STK (spZ regs) [] ly S W mem md [(1, fpos)] ly3 S3 mdX k
TRAWNEW_STK [] EV_RAWNEW (-192) (ew Ex 2) (Z_to_bv 64 0x86040) ((spZ regs, raZ regs, s0Z regs) :: ch)
(fun ly2 S2 W2 regs2 mem2 md2 => exists res : Z, getr regs2 10 = w64 res /\
((res = 0 /\ Permutation (ablocks B ly2 S2) (ablocks B ly3 S3)) \/
(res <> 0 /\ sgct <= 256 /\
Permutation (ablocks B ly2 S2) ((res, RAW_SIZE) :: ablocks B ly3 S3) /\
(forall blc i, In (res, RAW_SIZE) blc -> 0 <= i < RAW_SIZE ->
awr_byte TRAWNEW_STK (spZ regs - 192) [] (ablocks B ly3 S3) blc ly2 [] (res + i)) /\
aftok [] (ablocks B ly3 S3) (res, RAW_SIZE) /\
obj_at trbsegs (mrestrict (w_H W2) mem2) res LAY_Raw [A_cgif_writecb; g; pal0; ng_rattr attr; Wd; Hd; sgct; loops; R_PENDING]))) HS eq_refl HJ3);
[ rewrite Rsp; cbn [sv_denot]; reflexivity
| reflexivity
| evalE AG
| reflexivity
| clear; lia
| unfold TRAWNEW_STK, ASTACK; clear; lia
| rewrite FFS; unfold TRAWNEW_STK, ASTACK; clear; lia
| rewrite Rgp; evalE AG; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp
| rewrite Rtp; evalE AG; rewrite (EE 4%nat 4%bv eq_refl); exact Htp
| exact Rra
| apply ret_ok_even; vm_compute; reflexivity
| rewrite unsigned_lit_small by (clear; lia); clear; lia
| unfold s0Z; rewrite Rs0; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 2%nat) by lia; rewrite Usp;
replace (spZ regs + -192) with (spZ regs - 192) by (clear; lia); exact (achain_ly_top ly ly3 _ _ _ _ Etop3 Hch1)
| intros HPRE1; eapply SRr_mono;
[ pose proof (RAWNEW ly3 S3 W3 (ms_regs msX) (ms_mem msX) mdX ((spZ regs, raZ regs, s0Z regs) :: ch) (F + 32) g pal0 (ng_rattr attr) Wd Hd sgct loops 0 restX HPRE1) as CALL;
unfold cfg_at, apost_base in CALL; cbn [ss_pc]; change (w64 A_cgif_raw_newgif) with (Z_to_bv 64 560544) in CALL;
apply CALL; clear CALL;
[ unfold spZ; rewrite Rsp; evalE AG; first [rewrite Z.add_mod by (clear; lia) | rewrite Zminus_mod]; rewrite Hal32; reflexivity
| unfold raZ at 1; rewrite Rra, unsigned_lit_small by (clear; lia); cbn [spine map fst snd]; fold (spine ch); rewrite <- ?Hra88; destruct Hspine as [Hs | Hs]; rewrite Hs; cbn; rewrite <- ?Hra88; tauto
| rewrite Hfrs3; cbn [length]; clear - Hroom; lia
| eapply arodata_ok_journal; [exact HJ3 | exact HROD]
| rewrite Ra0; cbn [sv_denot]; evalE AG
| split; [exists 1, fpos; split; [exact Hfin3 | split; [clear; lia | rewrite EFA3; fold F; split; [rewrite HFq; replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia; apply Z_mod_mult | change (fs_frame_bytes 1) with 128; clear; lia]]]
| split; [rewrite HFq; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by lia; apply Z_mod_mult | exact HRA40]]
| exact Ocfg
| exact HBL
| exact Gwfn | exact Gctx | clear; lia | exact Gfile
| exact HEVc | exact HLIVEc ]
| cbv beta; intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJc & HPc & res & Hres & HK4);
exists ly4, S4, regs4, mem4, md4; split; [rewrite Rra; reflexivity|]; split; [exact HJc|]; split; [exact HPc|]; exists res; split; [exact Hres | rewrite ?HspX in HK4; exact HK4] ]
| intros a Ha; exfalso; exact (inFP_nil a Ha) ]
| ] end end.
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJc & HP4 & res & Ha04 & Hres).
clear Ra0 Rra Rsp Rgp Rtp Rs0 Hch1 HUP Vra Vs0 ZS5 HRA40.
pose proof (proj1 HJ4) as HAR4. aconsts HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (EFL4 : forall c p, flag_addr ly4 c p = flag_addr ly c p) by (intros c p; unfold flag_addr; pose proof (EFA4 c p) as X; unfold frame_addr in X; lia).
pose proof HJc as (_ & _ & _ & _ & _ & Hfrs4 & _). cbn [app] in Hfrs4.
assert (Hfin4 : In (1, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (HfinS4 : In (cid, pos) (frames S4)) by (rewrite Hfrs4; exact HfinS3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4). change (fs_frame_bytes 1) with 128 in HFpres4, HFSpres4.
change (128 / 8) with 16 in HFSpres4. rewrite !EFA4 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR4 HfinS4) as (_ & _ & HCpres4 & _). rewrite EFA4 in HCpres4.
destruct Hres as [(Hres0 & HPerm4) | (Hresnz & Hsg & HPerm4 & Araw & Traw & Oraw)].
+
assert (Hg_in4 : In (g, 96) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm4 | exact Hg_in]).
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11]%nat AG
ltac:(idtac; first [ keptJ HJc HJ4 AG Usp E10 RF E58 Hfin3 HfinS3 FFS Kgot3 Kgot4 Kcell3 Kcell4 Kguar3 Kguar4 Kuar3 Kuar4 Vgr3 Vgr4 EFA3 HFpres4 HFSpres4 HCpres4 F ltac:(fail)
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
pose proof (st_ok_pin_reg' trbsegs _ _ _ (10%bv : bv 5) 0 HS ltac:(cbn [ms_regs restrict mkst]; rewrite Ha04, Hres0; reflexivity) eq_refl) as HS3.
clear HS. rename HS3 into HS. norm_ss HS. reshok_bx HS 35%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ4 SHOK NBspan A_freeCGIF; [slim; awrR AG fpos F EFA4 |]. clear_frames.
pose (palv := pal0).
assert (Vpal24 : True) by exact I.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 79%nat in let i := eval vm_compute in i in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W4) msX) i _ HS eq_refl) as HRg; cbn [ms_mem restrict] in HRg;
assert (HB79' : bv_unsigned (ew Ex 79) = g) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by nat_side; rewrite Rg; apply unsigned_lit_small; clear - Hg4096 Hgceil C1; lia);
lazymatch type of HRg with region_ok _ _ _ (YQ0b.mkRegion (Some 79%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 79 g cs lo hi wlo whi 24 8%N (SOff 32 0) pal0 HRg HB79' ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by nat_side; rewrite (AG 32%nat) by lia; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; clear - CR0; lia) ltac:(cbn; lia)) as Gpal;
pose proof (field_of_region Ex _ 79 g cs lo hi wlo whi 40 4%N (SOff 33 0) attr HRg HB79' ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by nat_side; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; clear - CR16; lia) ltac:(cbn; lia)) as Gattr
end; clear HRg end.
cbn [N.to_nat] in Gpal, Gattr.
assert (HBL4 : Permutation (ablocks B ly4 S4) (fc_blocks g palv attr ngp ++ ablocks B ly S)).
{ unfold fc_blocks. replace (Z.land attr 4 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ha4). cbn [app].
eapply Permutation_trans; [exact HPerm4 | exact HBL]. }
assert (HEV4 : vev S4 + 2 <= VEV_MAX).
{ pose proof HJ4 as (_ & _ & _ & _ & _ & _ & Hnev4 & _). rewrite HEV in Hev. unfold EV_RAWNEW in Hnev4. clear - Hnev4 Hk3 Hev. lia. }
clear Kgot4 Kcell4 Kguar4 Kuar4 Vgr4. aconsts HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4.
rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp.
rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
ng_chain HS HJ4 AG EE.
pose proof (proj1 (proj2 HJ4)) as HLY4. pose proof HLY4 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop4 & _).
assert (HU1 : In [pc_free_ra0 Trb_code; 0x86400] (as_universe B)) by (rewrite (tl_universe B TL); apply memZL_In; vm_compute; reflexivity).
lazymatch type of HS with st_ok _ ?Ex ?ssX (restrict _ ?msX) =>
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdX) _ =>
eapply SRr_bind;
[ eapply (aj_call trbsegs B LAWS trb_segs_low W4 Ex ssX msX TNEWGIF_STK (spZ regs) [] ly S W mem md [(1, fpos)] ly4 S4 mdX (k + EV_RAWNEW)
FC_STK (ablocks_fp (fc_blocks g palv attr ngp)) 2 (-192) (ew Ex 2) (Z_to_bv 64 0x8609c) ((spZ regs, raZ regs, s0Z regs) :: ch)
(fun ly2 S2 W2 regs2 mem2 md2 => Permutation (ablocks B ly2 S2) (ablocks B ly S)) HS eq_refl HJ4);
[ rewrite Rsp; cbn [sv_denot]; reflexivity
| reflexivity
| evalE AG
| reflexivity
| clear; lia
| unfold FC_STK, ASTACK; clear; lia
| rewrite FFS; unfold FC_STK, ASTACK; clear; lia
| rewrite Rgp; evalE AG; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp
| rewrite Rtp; evalE AG; rewrite (EE 4%nat 4%bv eq_refl); exact Htp
| exact Rra
| apply ret_ok_even; vm_compute; reflexivity
| rewrite unsigned_lit_small by (clear; lia); clear; lia
| unfold s0Z; rewrite Rs0; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by nat_side; rewrite (AG 2%nat) by lia; rewrite Usp;
replace (spZ regs + -192) with (spZ regs - 192) by (clear; lia); exact (achain_ly_top ly ly4 _ _ _ _ Etop4 Hch1)
| intros HPRE1; eapply SRr_mono;
[ eapply (trb_freeCGIF B TL LAWS ML AFREE W4 ly4 S4 (ms_regs msX) (ms_mem msX) mdX _ g palv attr ngp (ablocks B ly S) HPRE1 HEV4);
[ rewrite Ra0; cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by nat_side; rewrite Rg; reflexivity
| exact Gpal | exact Gattr
| clear - CR0; lia
| clear - CR16; lia | clear - CR28; lia
| exact HBL4 | exact HU1
| rewrite call_trace_of_spine; cbn [spine map fst snd]; fold (spine ch); unfold raZ at 1; rewrite Rra, unsigned_lit_small by (clear; lia); rewrite <- Hra88;
rewrite (tl_universe B TL); apply TRACES_freeCGIF_U; apply memZL_In; destruct Hspine as [Hsp | Hsp]; rewrite Hsp; vm_compute; reflexivity ]
| cbv beta; unfold fc_post; intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ1 & HP & HK);
exists ly5, S5, regs5, mem5, md5; split; [rewrite Rra; reflexivity | split; [exact HJ1 | split; [exact HP | exact HK]]] ]
| intros a Ha; right; destruct (inFP_ablocks_fp_inv _ a Ha) as (p & n & Hpn & Hpa); exists p, n;
unfold fc_blocks in Hpn;
replace (Z.land attr 4 =? 0) with false in Hpn by (symmetry; apply Z.eqb_neq; exact Ha4); cbn [app In] in Hpn;
destruct Hpn as [Hpn | []]; injection Hpn as <- <-;
split; [exact Hg_in4 | split; [intros Hin0; exact (inFP_nil _ (Tg Hin0 0 ltac:(cbn [fst snd]; change (req_size 96) with 96; clear; lia))) | exact Hpa]]
]
| ] end end.
cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HJc5 & HP5 & HPerm5).
clear Ra0 Rra Rsp Rgp Rtp Rs0 Hch1 HUP Vra Vs0.
pose proof (proj1 HJ5) as HAR5. aconsts HROD HJ5 Kgot5 Kcell5 Kguar5 Kuar5 Vgr5.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly5 HAR (proj1 (proj2 HJ5))) as (_ & EFA5 & _).
assert (EFL5 : forall c p, flag_addr ly5 c p = flag_addr ly c p) by (intros c p; unfold flag_addr; pose proof (EFA5 c p) as X; unfold frame_addr in X; lia).
pose proof HJc5 as (_ & _ & _ & _ & _ & Hfrs5 & _). cbn [app] in Hfrs5.
assert (Hfin5 : In (1, fpos) (frames S5)) by (rewrite Hfrs5; exact Hfin4).
assert (HfinS5 : In (cid, pos) (frames S5)) by (rewrite Hfrs5; exact HfinS4).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR5 Hfin5) as (_ & _ & HFpres5 & HFSpres5). change (fs_frame_bytes 1) with 128 in HFpres5, HFSpres5.
change (128 / 8) with 16 in HFSpres5. rewrite !EFA5 in HFpres5, HFSpres5. fold F in HFpres5, HFSpres5.
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR5 HfinS5) as (_ & _ & HCpres5 & _). rewrite EFA5 in HCpres5.
assert (HnFP : forall a, inFP (ablocks_fp (fc_blocks g palv attr ngp)) a -> (g <= a < g + 96)
).
{ intros a Ha. destruct (inFP_ablocks_fp_inv _ a Ha) as (p & n & Hpn & Hpa). unfold fc_blocks in Hpn.
replace (Z.land attr 4 =? 0) with false in Hpn by (symmetry; apply Z.eqb_neq; exact Ha4). cbn [app In] in Hpn.
destruct Hpn as [Hpn | []]; injection Hpn as <- <-. change (req_size CGIF_OBJ) with 96 in Hpa. exact Hpa. }
reseat HS HJ5 HP5 [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11]%nat AG
ltac:(idtac; first [ keptJ HJc5 HJ5 AG Usp E10 RF E58 Hfin4 HfinS4 FFS Kgot4 Kgot5 Kcell4 Kcell5 Kguar4 Kguar5 Kuar4 Kuar5 Vgr4 Vgr5 EFA4 HFpres5 HFSpres5 HCpres5 F
ltac:(let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in intros a Ha Hn; apply HnFP in Hn;
clear - Ha Hn HdGF HdGC Hflo Hfhi Hfhigh Hcal Hfal Hgh Hgh_img Hgh_ia Hg4096 Hgceil HFceil HF4096 HFq HF8 Hf4096 Hfceil C1 C2 C3 C4 C5; nunbox HdGF; nunbox HdGC; unfold SB in Ha; zone_lia)
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
nbox_seps.
reshok_bx HS 35%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ5 SHOK NBspan 0x860c0; [slim; awrR AG fpos F EFA5|]. clear_frames.
exitN HS HJ5 AG fpos F cfgp E57 E58 Hfin5 HfinS5 EE Hra HEV EFA5 EFL5.
exists 0. split; [reflexivity|]. left. split; [reflexivity|].
unfold ablocks. rewrite blocks_stack_free_state. fold (ablocks B ly5 S5). exact HPerm5.
+
assert (Hr_in4 : In (res, RAW_SIZE) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm4 | left; reflexivity]).
assert (Hg_in4 : In (g, 96) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm4 | right; exact Hg_in]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res RAW_SIZE HAR4 Hr_in4) as (Hr16 & Hr4096 & Hrceil & Hrh_ia & Hrpres4 & _). pose proof (proj1 Hrh_ia) as Hrh.
pose proof (blk_off_img _ _ _ _ _ _ res RAW_SIZE HAR4 Hr_in4) as Hrh_img.
change (req_size RAW_SIZE) with 48 in Hrceil, Hrpres4, Hrh_img.
destruct (al_blocks _ _ LAWS _ _ _ _ _ g 96 HAR4 Hg_in4) as (_ & _ & _ & _ & Hgpres4 & _). change (req_size 96) with 96 in Hgpres4.
assert (HPerm4' : Permutation (ablocks B ly4 S4) ((res, RAW_SIZE) :: (g, CGIF_SIZE) :: restX)) by (eapply Permutation_trans; [exact HPerm4 | apply perm_skip; exact HBL]).
pose proof (sep_blocks_perm trbsegs B LAWS ly4 S4 _ _ _ (res, RAW_SIZE) (g, CGIF_SIZE) _ HAR4 HPerm4') as HdRG.
unfold zdisjoint, block_rng in HdRG. cbn [fst snd] in HdRG. change (req_size RAW_SIZE) with 48 in HdRG. change (req_size CGIF_SIZE) with 96 in HdRG.
pose proof (sep_block_frame trbsegs B LAWS ly4 S4 _ _ _ res RAW_SIZE 1 fpos HAR4 Hr_in4 Hfin4) as HdRF.
unfold zdisjoint in HdRF. cbn [fst snd] in HdRF. change (req_size RAW_SIZE) with 48 in HdRF. change (fs_frame_bytes 1) with 128 in HdRF. rewrite EFA4 in HdRF. fold F in HdRF.
pose proof (sep_block_frame trbsegs B LAWS ly4 S4 _ _ _ res RAW_SIZE cid pos HAR4 Hr_in4 HfinS4) as HdRC.
unfold zdisjoint in HdRC. cbn [fst snd] in HdRC. change (req_size RAW_SIZE) with 48 in HdRC. rewrite EFA4 in HdRC.
nbox_seps.
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11]%nat AG
ltac:(idtac; first [ keptJ HJc HJ4 AG Usp E10 RF E58 Hfin3 HfinS3 FFS Kgot3 Kgot4 Kcell3 Kcell4 Kguar3 Kguar4 Kuar3 Kuar4 Vgr3 Vgr4 EFA3 HFpres4 HFSpres4 HCpres4 F ltac:(fail)
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
rreg HS (10%bv : bv 5) Rr. cbn [ms_regs] in Rr. rewrite Ha04 in Rr. symmetry in Rr. unfold w64 in Rr.
lazymatch type of Rr with ew ?Ex ?nx = _ =>
pose proof (st_ok_add_fact trbsegs Ex _ _ nx (HPTR 4) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite Rr, unsigned_lit_small by (clear - Hr4096 Hrceil C1; lia); change (2 ^ 4) with 16;
clear - Hr16 Hr4096 Hrceil Hrh C1 C3; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok_bx HS 35%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ4 SHOK NBspan 0x860c0.
all: try (slim; obl_blk HJ4 Rg E35 Hg_in4).
all: try (slim; awrR AG fpos F EFA4).
lazymatch goal with HFr : frame_of _ _ _ _ |- _ =>
pose proof (kept_of_frame _ _ _ _ _ (fun a => (g <= a < g + 96) \/ (F <= a < F + 128) \/ (spZ regs - 192 <= a < spZ regs)) HFr
ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hrr; revert Hrr; evalE AG;
first [rewrite Rg | rewrite RF | idtac]; rewrite ?unsigned_lit_small by lia; intros Hrr; clear - Hrr; lia |]);
destruct Hin)) as UN1 end.
clear_frames.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 79%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
pose proof (ast_ok_set_region trbsegs Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow trbsegs Ex _ r 0 0 (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
reshok_bx HS 35%nat.
assert (HnoG : forall a, g <= a < g + 96 -> ~ aowned B ly4 S4 a) by (intros a Ha; exact (proj2 (Hgpres4 a Ha))).
assert (HnoR : forall a, res <= a < res + 48 -> ~ aowned B ly4 S4 a) by (intros a Ha; exact (proj2 (Hrpres4 a Ha))).
exitN HS HJ4 AG fpos F cfgp E57 E58 Hfin4 HfinS4 EE Hra HEV EFA4 EFL4.
exists g. split; [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by nat_side; rewrite Rg; reflexivity|].
right. split; [clear - Hg4096; lia|].
exists (mkCgif [None; None; None] pal0 attr gen Wd Hd ngp loops res R_PENDING 1 pal0 (ng_rattr attr) loops R_PENDING).
split.
{
split; [|split].
- lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 79%nat in let i := eval vm_compute in i in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W4) msX) i _ HS eq_refl) as HRgf; cbn [ms_mem restrict] in HRgf;
assert (HB79f : bv_unsigned (ew Ex 79) = g) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by nat_side; rewrite Rg; apply unsigned_lit_small; clear - Hg4096 Hgceil C1; lia) end.
lazymatch type of HRgf with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 79%nat) ?lo ?hi ?wlo ?whi ?cs) =>
let lit off n v Rt Q := pose proof (field_of_region Ex _ 79 g cs lo hi wlo whi off n (SLit v) v HRgf HB79f ltac:(cbn; tauto) eq_refl ltac:(Rt) ltac:(cbn; lia)) as Q in
let atm off n e v He Rt Q := pose proof (field_of_region Ex _ 79 g cs lo hi wlo whi off n e v HRgf HB79f ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by nat_side;
rewrite ?(AG 32%nat) by lia; rewrite He, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(Rt) ltac:(cbn; lia)) as Q in
lit 0 8%N 0 ltac:(zside) Q0; lit 8 8%N 0 ltac:(zside) Q8; lit 16 8%N 0 ltac:(zside) Q16;
atm 24 8%N (SOff 32 0) pal0 E32 ltac:(cbn; clear - CR0; lia) Q24;
lit 32 8%N 0 ltac:(zside) Q32;
atm 40 4%N (SOff 33 0) attr E33 ltac:(cbn; clear - CR16; lia) Q40; atm 44 4%N (SOff 34 0) gen E34 ltac:(cbn; clear - CR20; lia) Q44;
atm 48 2%N (SOff 36 0) Wd E36 ltac:(cbn; clear - CR24; lia) Q48; atm 50 2%N (SOff 37 0) Hd E37 ltac:(cbn; clear - CR26; lia) Q50;
atm 52 2%N (SOff 38 0) ngp E38 ltac:(cbn; clear - CR28; lia) Q52; atm 54 2%N (SOff 39 0) loops E39 ltac:(cbn; clear - CR30; lia) Q54;
lit 56 8%N A_writecb ltac:(unfold A_writecb; zside) Q56; lit 64 8%N 0 ltac:(zside) Q64;
lazymatch type of Rr with ew _ ?nr = _ => atm 72 8%N (SOff nr 0) res Rr ltac:(cbn; clear - Hr4096 Hrceil C1; lia) Q72 end;
lit 80 8%N 0 ltac:(zside) Q80; lit 88 4%N R_PENDING ltac:(unfold R_PENDING; zside) Q88; lit 92 4%N 1 ltac:(zside) Q92
end.
cbn [N.to_nat] in Q0, Q8, Q16, Q24, Q32, Q40, Q44, Q48, Q50, Q52, Q54, Q56, Q64, Q72, Q80, Q88, Q92.
unfold tcgif_vals, cg_frames, cg_pal, cg_attr, cg_gen, cg_W, cg_H, cg_ngp, cg_loops, cg_raw, cg_cur, cg_ihead. cbn [nth frame_ptr obj_at LAY_CGIF].
unfold field_ok. cbn [fst snd N.to_nat Z.of_N].
change (2 ^ (8 * 8)) with (2 ^ 64). change (2 ^ (8 * 4)) with (2 ^ 32). change (2 ^ (8 * 2)) with 65536.
repeat split; try assumption;
first [unfold A_writecb, R_PENDING; clear; lia | clear - CR0 CR16 CR20 CR24 CR26 CR28 CR30 Hg4096 Hgceil Hr4096 Hrceil C1; lia
| match goal with |- ?G => idtac "OBJLEFT" G end].
-
lazymatch goal with HFr : frame_of _ _ _ _ |- _ =>
pose proof (kept_of_frame _ _ _ _ _ (fun a => (FL <= a < FL + 1) \/ (SB + F / 8 <= a < SB + F / 8 + 16) \/ (F <= a < F + 128) \/ (spZ regs - 192 <= a < spZ regs)) HFr
ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hrr; revert Hrr; evalE AG;
first [rewrite Rg | rewrite RF | idtac]; rewrite ?unsigned_lit_small by lia; intros Hrr; clear - Hrr; lia |]);
destruct Hin)) as UN2 end.
lazymatch goal with |- obj_at _ (mrestrict _ ?mF) _ _ _ =>
assert (KR : blk_kept (w_H W4) (w_H W4) mem4 mF res 48) end.
{ intros i Hi.
assert (Hb : 0 <= res + i < 2 ^ 64) by (clear - Hi Hr4096 Hrceil C1; lia).
rewrite (UN2 (res + i) Hb).
- apply (UN1 (res + i) Hb). clear - Hi HdRG HdRF Hrceil Hceil Hslo FFS. nunbox HdRG. nunbox HdRF. lia.
- intros [Hq | Hq].
+ apply (proj2 (Hrpres4 (res + i) ltac:(clear - Hi; lia))). replace (res + i) with FL by (clear - Hq; lia). exact HFLown'.
+ clear - Hq Hi HdRF Hrceil Hceil Hslo FFS HFq HF8 HF8lo HFceil Hrh Hrh_ia C1 C3. nunbox HdRF. unfold SB in Hq. zone_lia. }
unfold traw_vals, rw_gct, rw_attr, cg_W, cg_H, raw_sgct, cg_attr, cg_ngp, rw_loops, rw_cur.
replace (Z.land attr 4 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ha4).
exact (obj_at_blk_kept _ _ _ _ res LAY_Raw _ 48 Oraw lay_inside_Raw KR).
- intros f Hf. exfalso. cbn in Hf. destruct Hf as [Hf | [Hf | [Hf | []]]]; discriminate Hf. }
split.
{ unfold cgif_wf, cg_frames, cg_W, cg_H, cg_attr, cg_ngp, cg_ihead. cbn [length nth].
split; [reflexivity|]. split; [clear - HW0 CR24; lia|]. split; [clear - HH0 CR26; lia|]. split; [reflexivity|]. split; [exact HWH|].
split; [intros Hc; exfalso; exact (Ha4 Hc)|].
split; [left; reflexivity|].
intros f Hf. exfalso. cbn in Hf. destruct Hf as [Hf | [Hf | [Hf | []]]]; discriminate Hf. }
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split.
{
unfold ablocks. rewrite blocks_stack_free_state. fold (ablocks B ly4 S4).
unfold cgif_blocks, pal_blocks, frames_blocks, cg_frames, cg_raw, cg_attr, cg_pal, cg_ngp.
replace (Z.land attr 4 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ha4). cbn [flat_map app].
eapply Permutation_trans; [exact HPerm4'|]. subst restX. apply perm_swap. }
intros b Hb. unfold cgif_blocks, pal_blocks, frames_blocks, cg_frames, cg_raw, cg_attr, cg_pal, cg_ngp in Hb.
replace (Z.land attr 4 =? 0) with false in Hb by (symmetry; apply Z.eqb_neq; exact Ha4). cbn [flat_map app In] in Hb.
destruct Hb as [<- | [<- | []]]; cbn [fst snd].
* split; [exact Tg | intros blc i Hbl Hi; apply Ag; [exact Hbl | exact Hi]].
* split.
-- intros Hin0 i Hi. apply Traw; [| exact Hi]. rewrite Eab3. apply in_app_iff. left.
exact Hin0.
-- intros blc i Hbl Hi. apply (awr_byte_callee0 TNEWGIF_STK TRAWNEW_STK (spZ regs) (spZ regs - 192) (ablocks B ly S) (ablocks B ly3 S3) blc ly4 ly4 (res + i));
[ apply Araw; [exact Hbl | exact Hi] | unfold TNEWGIF_STK, TRAWNEW_STK; clear; lia | clear; lia
| intros x Hx; rewrite Eab3; apply in_app_iff; left; exact Hx ].
Qed.
End h. End d.
