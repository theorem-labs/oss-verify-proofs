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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCfu YCe9 YChv YChx YChw.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma range_addressable_zero8 : forall (rd : Z -> option Z) Bs p,
rd (shadow_of_addr Bs p) = Some 0 -> p mod 8 = 0 -> range_addressable rd Bs p 8.
Proof.
intros rd Bs p Hz Hp. apply zero_shadow_range; [exact Hp | reflexivity |].
intros i Hi. change (8 / 8) with 1 in Hi. replace i with 0 by lia. rewrite Z.add_0_r. exact Hz.
Qed.
Section d.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMSET : aintrin_realizes trbsegs B OSet A_asan_memset.
Hypothesis ASF : astack_free_law trbsegs B.
Hypothesis FFL : frame_flag_lawP trbsegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rn_B : rn_from B ss_C -> rn_from B ss_B.
Proof.
intros RC ly S W regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx rest cid pos E0 E W3 ly3 S3 ms3 md3 k fpos res
HPRE Hal32 HROD HCFG Hcfg HPerm Hev HE0 HE HNOW Hsg HS.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (FFS : TRAWNEW_STK = 16576) by reflexivity.
assert (HEV : EV_RAWNEW = 4) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct HCFG as (Hfin & Hcid0 & Hfal & Hflo & Hfhi & Hcal & HRA).
destruct HE0 as (EE & E10 & E32 & Usp). destruct HE as (AG & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & RF & E57 & E58 & Rres).
destruct HNOW as (HJ3 & Hk3 & Hfrs3 & Eab3 & Hres4096 & Tres & Ares).
pose proof (proj1 HJ3) as HAR3.
destruct (frames_bounds trbsegs B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img.
assert (Hing : In (g, CGIF_SIZE) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W mem md g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, Hgh_img.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR (proj1 (proj2 HJ3))) as (_ & EFA3 & _).
assert (EFL3 : forall c p, flag_addr ly3 c p = flag_addr ly c p) by (intros c p; unfold flag_addr; pose proof (EFA3 c p) as X; unfold frame_addr in X; lia).
assert (Hfin3 : In (2, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
assert (HfinS3 : In (cid, pos) (frames S3)) by (rewrite Hfrs3; right; exact Hfin).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR3 Hfin3) as (HFal & [HFhi _] & HFpres3 & HFSpres3).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR3 Hfin3) as HFapp_img.
destruct (frames_bounds trbsegs B LAWS _ _ _ _ _ 2 fpos HAR3 Hfin3) as (HF4096 & HFceil & HFhigh).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR3 Hfin3) as HFhigh_img.
change (fs_frame_bytes 2) with 256 in *. change (256 / 8) with 32 in HFSpres3. rewrite !EFA3 in *.
set (F := frame_addr ly 2 fpos) in *. set (FL := flag_addr ly 2 fpos) in *.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia)    .
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
assert (Hres_in : In (res, 48) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_app_iff; right; left; reflexivity).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_app_iff; left; exact Hing).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res 48 HAR3 Hres_in) as (Hr16 & Hr4096 & Hrceil & Hrh_ia & Hrpres3 & _). pose proof (proj1 Hrh_ia) as Hrh.
pose proof (blk_off_img _ _ _ _ _ _ res 48 HAR3 Hres_in) as Hrh_img.
change (req_size 48) with 48 in Hrceil, Hrpres3, Hrh_img.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ res 48 2 fpos HAR3 Hres_in Hfin3) as HdRF.
unfold zdisjoint in HdRF. cbn [fst snd] in HdRF. change (req_size 48) with 48 in HdRF. change (fs_frame_bytes 2) with 256 in HdRF. rewrite EFA3 in HdRF. fold F in HdRF.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ res 48 cid pos HAR3 Hres_in HfinS3) as HdRC.
unfold zdisjoint in HdRC. cbn [fst snd] in HdRC. change (req_size 48) with 48 in HdRC. rewrite EFA3 in HdRC.
pose proof (sep_blocks trbsegs B LAWS ly3 S3 _ _ _ g CGIF_SIZE res 48 HAR3 Hing3 Hres_in ltac:(unfold CGIF_SIZE; intros X; injection X; lia)) as HdRG.
unfold zdisjoint in HdRG. cbn [fst snd] in HdRG. change (req_size 48) with 48 in HdRG. change (req_size CGIF_SIZE) with 96 in HdRG.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ g CGIF_SIZE 2 fpos HAR3 Hing3 Hfin3) as HdFG.
unfold zdisjoint in HdFG. cbn [fst snd] in HdFG. change (req_size CGIF_SIZE) with 96 in HdFG. change (fs_frame_bytes 2) with 256 in HdFG. rewrite EFA3 in HdFG. fold F in HdFG.
destruct (in_split _ _ Hfin) as (fl1 & fl2 & Efl).
pose proof (sep_frames_pos trbsegs B LAWS ly3 S3 _ _ _ (2, fpos) (cid, pos) [] fl1 fl2 HAR3 ltac:(rewrite Hfrs3, Efl; reflexivity)) as HdFC.
unfold zdisjoint, frame_rng in HdFC. cbn [fst snd] in HdFC. change (fs_frame_bytes 2) with 256 in HdFC. rewrite !EFA3 in HdFC. fold F in HdFC.
aconsts HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (st_ok_submem trbsegs E ssx msx
(nth 0 (ss_mem ssx) got_region :: nth 1 (ss_mem ssx) got_region :: trim_lo (nth 2 (ss_mem ssx) got_region) 125 :: skipn 3 (ss_mem ssx)) HS
ltac:(cbn [ss_mem ss_B nth skipn]; apply submem_keep; [apply subregion_refl|]; apply submem_keep; [apply subregion_refl|];
apply submem_keep; [apply subregion_trim_lo|]; apply submem_refl) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ _ _ _ =>
pose proof (ast_ok_add_region trbsegs E _ _ (YQ0b.mkRegion (Some 45%nat) 0 113 0 113 []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (HFpres3 (F + o) ltac:(lia))))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite RF; evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rawnew, CGIF_SIZE; repeat split; first [zone_lia | match goal with |- ?g => idtac "DISJ" g; fail end])) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ _ _ _ =>
pose proof (ast_ok_add_region trbsegs E _ _ (YQ0b.mkRegion (Some 45%nat) 113 125 113 125 []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (HFpres3 (F + o) ltac:(lia))))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite RF; evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rawnew, CGIF_SIZE; repeat split; first [zone_lia | match goal with |- ?g => idtac "DISJ" g; fail end])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok_bx HS 35%nat.
assert (E10' : ew E 10 = Z_to_bv 64 cfgp) by (rewrite (AG 10%nat) by lia; exact E10).
assert (EFA0 : forall c p, frame_addr ly3 c p = frame_addr ly c p) by exact EFA3.
aj_run_tok trbtbl_lib_ok HS HJ3 SHOK RBspan;
[ oblF HJ3 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal | oblF HJ3 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal | awrR AG fpos F EFA3 |].
clear HF HG.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) 3 _ HS eq_refl) as HRfs; cbn [ms_mem restrict] in HRfs;
lazymatch type of HRfs with region_ok _ _ _ (YQ0b.mkRegion (Some 58%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 58 (SB + F / 8) cs lo hi wlo whi 14 1%N (SLit 0) 0 HRfs
ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V14;
pose proof (field_of_region Ex _ 58 (SB + F / 8) cs lo hi wlo whi 15 1%N (SLit 5) 5 HRfs
ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V15 end;
clear HRfs;
pose proof (aview_of_val_mem1 trbsegs _ _ _ _ V14 ltac:(lia)) as Hsh14;
pose proof (aview_of_val_mem1 trbsegs _ _ _ _ V15 ltac:(lia)) as Hsh15;
assert (HRA3 : range_addressable (aview trbsegs (w_H W3) (ms_mem msX)) SHADOW_OFF (F + 113) 12);
[ eapply (range_addressable_sub (aview trbsegs (w_H W3) (ms_mem msX)) SHADOW_OFF (F + 112) 13); [|lia|lia];
replace 13 with (8 + 5) by reflexivity; apply range_addressable_app; [lia| |];
[ apply range_addressable_zero8; [|rewrite HFq; replace (32 * (F / 32) + 112) with ((4 * (F / 32) + 14) * 8) by lia; apply Z_mod_mult];
rewrite <- Hsh14; unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF; f_equal; rewrite HFq at 1; rewrite HF8;
replace (32 * (F / 32) + 112) with ((4 * (F / 32) + 14) * 8) by lia; rewrite Z.div_mul by lia; lia
| replace (F + 112 + 8) with (F + 120) by lia;
eapply (range_addressable_partial _ SHADOW_OFF (F + 120) 5); [|rewrite HFq; replace (32 * (F / 32) + 120) with ((4 * (F / 32) + 15) * 8) by lia; apply Z_mod_mult|lia];
rewrite <- Hsh15; unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF; f_equal; rewrite HFq at 1; rewrite HF8;
replace (32 * (F / 32) + 120) with ((4 * (F / 32) + 15) * 8) by lia; rewrite Z.div_mul by lia; lia ]
| ] end.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 337168) with (Z_to_bv 64 A_asan_memset).
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3. aconsts HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_at trbsegs B LAWS Hsegs OSet A_asan_memset AMEMSET _ (ms_regs msX) (ms_mem msX) TRAWNEW_STK (spZ regs) [] ly S W mem md [(2, fpos)]
ly3 S3 _ _ (F + 113) 0 12 (-192) (Z_to_bv 64 0x88f6c) HJ3) end.
- rewrite Ra0. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite RF. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
- exact Ra1.
- exact Ra2.
- lia. - lia. - lia.
- unfold spZ at 1. rewrite Rsp. evalE AG.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- intros a Ha. split; [| unfold ESTACK; lia]. right. right. right. exists 2, fpos. split; [left; reflexivity|]. left.
unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 2) with 256. rewrite EFA3. fold F. lia.
- apply amem_range_high; zone_lia.
- exact HRA3.
- intros _. eapply (shadow_hull_vis_of_frame trbsegs B LAWS ly3 S3 _ _ _ 2 fpos (F + 113) 12 (proj1 HJ3) Hfin3);
[rewrite EFA3; fold F; lia | rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; lia | lia].
- exact I. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff & Hfr4 & Hpres4).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp V14 V15 Hsh14 Hsh15 HRA3.
aconsts HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ4) Hfin3) as (_ & _ & HFpres4 & HFSpres4). change (fs_frame_bytes 2) with 256 in HFpres4, HFSpres4.
change (256 / 8) with 32 in HFSpres4. rewrite !EFA3 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
reseat HS HJ4 HP4 [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12]%nat AG
ltac:(idtac; first [ keptI Hfr4 Hpres4 AG Kgot3 Kgot4 Kcell3 Kcell4 Kguar3 Kguar4 Kuar3 Kuar4 Vgr3 Vgr4
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region trbsegs Ev _ _ (YQ0b.mkRegion (Some 45%nat) 113 125 113 125 []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (HFpres4 (F + o) ltac:(lia))))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite RF; evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rawnew, CGIF_SIZE; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok_bx HS 35%nat. clear_frames.
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
assert (E10'' : ew Ev 10 = Z_to_bv 64 cfgp) by (rewrite (AG 10%nat) by lia; exact E10) end.
aj_run_tok trbtbl_lib_ok HS HJ4 SHOK RBspan; [oblF HJ4 E10'' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal | awrR AG fpos F EFA3 |].
clear_frames.
srr_branch_tok trbtbl_lib_ok HS SHOK RBspan.
-
aj_run_to_tok trbtbl_lib_ok HS HJ4 SHOK RBspan 0x8904c; [awrR AG fpos F EFA3|]. clear_frames.
norm_ss HS.
rn_join HS ss_C 160%nat rn_deads_C.
lazymatch type of HS with st_ok _ ?Ev _ (restrict _ ?msv) =>
eapply (RC ly S W regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx rest cid pos E0 Ev W3 ly3 S3 msv _ k fpos res);
[ exact HPRE | exact Hal32 | exact HROD | split; [exact Hfin | repeat (split; [eassumption|]); exact HRA] | exact Hcfg | exact HPerm | exact Hev
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| apply rn_E_havoc; [clear; lia | repeat (apply rn_E_ewset; [clear; lia|]); repeat (split; [eassumption|]); eassumption]
| split; [exact HJ4 | split; [exact Hk3 | split; [exact Hfrs3 | split; [exact Eab3 | split; [exact Hres4096 | split; [exact Tres | exact Ares]]]]]]
| exact Hsg | exact HS ] end.
-
pose proof Hcfg as Hc'. cbn [obj_at LAY_RawConfig] in Hc'. destruct Hc' as (_ & _ & _ & _ & _ & _ & [_ R32] & _). cbn [fst snd N.to_nat Z.of_N] in R32.
change (2 ^ (8 * 2)) with 65536 in R32.
unfold branch_taken in Hc. rewrite bv_eqb_unsigned in Hc. cbn [sv_denot] in Hc.
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hc. rewrite ?ew_ewset_other in Hc by lia.
rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.eqb_neq in Hc.
aj_run_to_tok trbtbl_lib_ok HS HJ4 SHOK RBspan 0x89018; [awrR AG fpos F EFA3|]. clear_frames.
rreg HS (11%bv : bv 5) Ra0. rreg HS (12%bv : bv 5) Ra1. rreg HS (13%bv : bv 5) Ra2. rreg HS (10%bv : bv 5) Rs5.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (rn_pow2a B LAWS 9 0 sgct W3 (ms_regs msX) (ms_mem msX) _ TRAWNEW_STK (spZ regs) [] ly S W mem md [(2, fpos)] ly3 S3 k eq_refl HJ4);
[ exact Ra0 | exact Ra1 | exact Ra2 | rewrite Rs5; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E38
| clear; lia | clear - Hc Hsg R32; lia | change (2 ^ 0) with 1; clear - Hc R32; lia ] end. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & K & -> & HJ5 & HK10 & HK13 & HKlo & HKs1 & HKs2 & Hav5 & Hpr5 & Hrg5).
clear Ra0 Ra1 Ra2 Rs5.
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K 0 (SOff 32 0) [] ssx) in
jafter_stretch HS kk regs5 (mrestrict (w_H W3) mem5) POW_CLOB_A 0x8902c HS2;
specialize (HS2 Hrg5 (regions_kept_all Ev (w_H W3) (ms_mem msX) mem5 _ Hav5 Hpr5)) end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS. rebaseE HS AG HEv. clear HEv.
norm_ss HS. reshok_bx HS 35%nat.
aj_run_tok trbtbl_lib_ok HS HJ5 SHOK RBspan; [awrR AG fpos F EFA3 |]. clear_frames.
srr_branch_tok trbtbl_lib_ok HS SHOK RBspan.
+ aj_run_to_tok trbtbl_lib_ok HS HJ5 SHOK RBspan 0x8904c; [awrR AG fpos F EFA3|]. clear_frames.
norm_ss HS.
rn_join HS ss_C 160%nat rn_deads_C.
lazymatch type of HS with st_ok _ ?Ev _ (restrict _ ?msv) =>
eapply (RC ly S W regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx rest cid pos E0 Ev W3 ly3 S3 msv _ k fpos res);
[ exact HPRE | exact Hal32 | exact HROD | split; [exact Hfin | repeat (split; [eassumption|]); exact HRA] | exact Hcfg | exact HPerm | exact Hev
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| apply rn_E_havoc; [clear; lia | repeat (apply rn_E_ewset; [clear; lia|]); repeat (split; [eassumption|]); eassumption]
| split; [exact HJ5 | split; [exact Hk3 | split; [exact Hfrs3 | split; [exact Eab3 | split; [exact Hres4096 | split; [exact Tres | exact Ares]]]]]]
| exact Hsg | exact HS ] end.
+ aj_run_to_tok trbtbl_lib_ok HS HJ5 SHOK RBspan 0x8904c; [awrR AG fpos F EFA3|]. clear_frames.
norm_ss HS.
rn_join HS ss_C 160%nat rn_deads_C.
lazymatch type of HS with st_ok _ ?Ev _ (restrict _ ?msv) =>
eapply (RC ly S W regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx rest cid pos E0 Ev W3 ly3 S3 msv _ k fpos res);
[ exact HPRE | exact Hal32 | exact HROD | split; [exact Hfin | repeat (split; [eassumption|]); exact HRA] | exact Hcfg | exact HPerm | exact Hev
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| apply rn_E_havoc; [clear; lia | repeat (apply rn_E_ewset; [clear; lia|]); repeat (split; [eassumption|]); eassumption]
| split; [exact HJ5 | split; [exact Hk3 | split; [exact Hfrs3 | split; [exact Eab3 | split; [exact Hres4096 | split; [exact Tres | exact Ares]]]]]]
| exact Hsg | exact HS ] end.
Qed.
End d.
End b.
