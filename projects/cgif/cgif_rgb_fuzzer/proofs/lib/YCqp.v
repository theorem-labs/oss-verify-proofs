(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0p YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI20.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCdv YCe9 YCfx YChv YChx YChi YChn YChg YCf6 YCft YCi1 YCie YCph YCrr YCrd YCrc YCrn YCr3 YCr9 YCr7 YCr4 YChy.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0n YG0o YG0t YG0r YG0q YC00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac nat_side := first [ apply (proj1 (Nat.ltb_lt _ _)); vm_compute; reflexivity
| apply (proj1 (Nat.eqb_neq _ _)); vm_compute; reflexivity
| cbn [length Nat.add]; apply (proj1 (Nat.leb_le _ _)); vm_compute; reflexivity ].
Ltac idx_of_baseLoR rs n lo :=
lazymatch rs with
| YQ0b.mkRegion (Some n) lo _ _ _ _ :: _ => constr:(0%nat)
| _ :: ?tl => let i := idx_of_baseLoR tl n lo in constr:(S i)
end.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section c.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis AMEMCPY : aintrin_realizes trbsegs B OCpy A_asan_memcpy_tfb.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.
Lemma rt_B1_aux : rt_from B ss_B2 (INV_Bn B 361) -> rt_from B ss_B1 (INV_0 B 0).
Proof.
intros RN. rt_prelude.
pose proof HINV as [Hk0 Eab3].
relowRT HS AG E10 E11 E32 E10n E11n E32n.
lazymatch type of HS with st_ok _ _ ?ssx _ =>
let rs := eval vm_compute in (ss_mem ssx) in let i := idx_of_baseLoR rs 75%nat 32 in let i := eval vm_compute in i in trim_nth HS i 32 56 end.
reshok HS.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK RTBspan A_readdata.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRT AG fpos F EFA3.
clear_frames.
assert (Hp_rng : 0 <= p < 2 ^ 64).
{ destruct Hpn as [[_ ->] | [Hn' Hin]]; [unfold A_EMPTY; clear; lia|].
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & Hp4096 & Hpceil & _). pose proof (req_size_pos n ltac:(clear - Hn'; lia)) as [Hq1 _]. clear - Hp4096 Hpceil Hq1 C1. lia. }
assert (B70 : bv_unsigned (ew E 70) = sp1) by (rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 70%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRL; cbn [ms_mem restrict] in HRL;
lazymatch type of HRL with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 70 sp1 cs lo hi wlo whi 32 8%N (SOff 10 0) p HRL B70 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite (AG 10%nat) by lia; rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hp_rng) ltac:(cbn; lia)) as Vp;
pose proof (field_of_region Ex _ 70 sp1 cs lo hi wlo whi 40 8%N (SOff 11 0) n HRL B70 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite (AG 11%nat) by lia; rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Hn26; lia) ltac:(cbn; lia)) as Vn;
pose proof (field_of_region Ex _ 70 sp1 cs lo hi wlo whi 48 8%N (SLit 0) 0 HRL B70 ltac:(cbn; tauto)
ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vc end;
clear HRL end.
change (N.to_nat 8) with 8%nat in Vp, Vn, Vc.
replace (sp1 + 40) with (sp1 + 32 + 8) in Vn by (clear; lia). replace (sp1 + 48) with (sp1 + 32 + 16) in Vc by (clear; lia).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msC) =>
assert (RA8 : range_addressable (aview trbsegs (w_H W3) (ms_mem msC)) SHADOW_OFF (F + 64) 8) end.
{ lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 88%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HR88; cbn [ms_mem restrict] in HR88 end.
apply zero_shadow_range; [replace (F + 64) with ((F / 8 + 8) * 8) by (clear - HFq HF8; lia); apply Z_mod_mult | reflexivity |].
intros i Hi. change (8 / 8) with 1 in Hi. assert (i = 0) by (clear - Hi; lia). subst i. unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF.
replace ((F + 64) / 8) with (F / 8 + 8) by (replace (F + 64) with ((F / 8 + 8) * 8) by (clear - HFq HF8; lia); rewrite Z.div_mul by (clear; lia); reflexivity).
replace (SB + (F / 8 + 8) + 0) with (SB + F / 8 + 8) by (clear; lia).
eapply (zs_chunk1 _ _ _ _ _ _ HR88); [cbn [base_val YQ0b.r_base]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E88; apply unsigned_lit_small; unfold SB; clear - HF8lo HF8hi; lia
| cbn; tauto | unfold SB; clear - HF8lo; lia | unfold SB; clear - HF8hi; lia]. }
assert (RAst : forall mm mdd, AR trbsegs B ly3 S3 W3 mm mdd -> range_addressable (aview trbsegs (w_H W3) mm) SHADOW_OFF (sp1 + 32) 24).
{ intros mm mdd HARm. pose proof (proj1 (proj2 HJ3)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
apply (RA_stack B LAWS ly3 S3 W3 mm mdd (sp1 + 32) 24 HARm); [rewrite Elo; clear - Hsp1 Hslo FFS; lia | rewrite Ehi; clear - Hsp1 Hshi; lia
| rewrite <- Zplus_mod_idemp_l; replace (sp1 mod 8) with 0 by (symmetry; pose proof (Z.div_mod sp1 32 ltac:(clear; lia)) as D; rewrite Hsp1al, Z.add_0_r in D; rewrite D; replace (32 * (sp1 / 32)) with ((4 * (sp1 / 32)) * 8) by (clear; lia); apply Z_mod_mult); reflexivity
| reflexivity | clear; lia]. }
assert (Dpf : p + n <= F + 66 \/ F + 66 + 2 <= p).
{ destruct Hpn as [[-> ->] | [Hn' Hin]]; [unfold A_EMPTY; clear - HFhigh_img; unfold off_img in HFhigh_img; lia|].
pose proof (sep_block_frame trbsegs B LAWS _ _ _ _ _ p n 2 fpos HAR3 ltac:(rewrite Eab3; exact Hin) Hfin3) as D. unfold zdisjoint in D. cbn [fst snd] in D.
rewrite EFA3 in D. fold F in D. change (fs_frame_bytes 2) with 256 in D. pose proof (req_size_pos n ltac:(clear - Hn'; lia)) as [_ Hq2]. clear - D Hq2. lia. }
lazymatch type of HS with st_ok _ _ ?ssx _ =>
let rs := eval vm_compute in (ss_mem ssx) in let i := idx_of_base rs 70%nat in let i := eval vm_compute in i in trim_nth HS i 0 48 end.
clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 531812) with (Z_to_bv 64 A_readdata).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (aj_readdata_at B TL LAWS AMEMCPY _ (ms_regs msX) (ms_mem msX) LLVMF_STK (spZ regs) [] ly S W mem md [(2, fpos)] ly3 S3 _ k
(sp1 + 32) (F + 66) 2 p n 0 (sp1 - spZ regs) _);
[ exact HJ3
| rewrite Ra0; evalE AG
| rewrite Ra1; evalE AG
| rewrite Ra2; reflexivity
| rewrite Rgp; evalE AG; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp
| rewrite Rtp; evalE AG; rewrite (EE 4%nat 4%bv eq_refl); exact Htp
| exact Rra
| vm_compute; reflexivity
| unfold spZ at 1; rewrite Rsp; evalE AG
| rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity
| clear - Hsp1; lia
| rewrite FFS, Hes; clear - Hsp1; lia
| rewrite <- Zplus_mod_idemp_l; replace (sp1 mod 8) with 0 by (symmetry; pose proof (Z.div_mod sp1 32 ltac:(clear; lia)) as D; rewrite Hsp1al, Z.add_0_r in D; rewrite D; replace (32 * (sp1 / 32)) with ((4 * (sp1 / 32)) * 8) by (clear; lia); apply Z_mod_mult); reflexivity
| clear; lia
| clear - Hsp1; lia
| exact (RAst _ _ (proj1 HJ3))
| exact Vp | exact Vn | exact Vc
| destruct Hpn as [[Hn0 Hp0] | [Hn' Hin]]; [right; split; [exact Hn0 | exact Hp0] | left; split; [clear - Hn'; lia | rewrite Eab3; exact Hin]]
| clear - Hn26; lia
| clear; lia | clear - HF4096; lia
| intros a Ha; split; [right; right; right; exists 2, fpos; split; [left; reflexivity | left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 2) with 256; rewrite ?EFA3; fold F; clear - Ha; lia]
| rewrite Hes; clear - Ha HFceil Hsp1 Hceil Hslo FFS C1; lia]
| apply amem_range_high; [clear; lia | clear - HFhigh HFhigh_img HFceil C1 C3; ceil; unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; zone_lia | clear - HFceil; lia]
| eapply range_addressable_sub; [exact RA8 | clear; lia | clear; lia]
| intros _; eapply (shadow_hull_vis_of_frame trbsegs B LAWS ly3 S3 _ _ _ 2 fpos (F + 66) 2 (proj1 HJ3) Hfin3);
[rewrite EFA3; fold F; clear; lia | rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear; lia | clear; lia]
| right; left; clear - HFceil Hsp1 Hceil Hslo FFS C1; lia
| clear - Dpf; lia ] end. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & r1 & cur1 & -> & HJ2 & HP2 & Ha02 & Hr1 & Vp' & Vn' & Vc' & Hfr2 & Hpres2).
rewrite Hes in Hfr2. replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hfr2 by (clear; lia).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp Vp Vn Vc RA8 RAst.
assert (Hcb1 : 0 <= cur1 <= n) by (clear - Hr1 Hn26; destruct Hr1 as [(_ & X & -> & _)|(_ & _ & -> & _)]; lia).
assert (Hr1v : 0 <= r1 < 2 ^ 64 /\ (r1 = 0 -> 2 <= n)) by (clear - Hr1; destruct Hr1 as [(-> & X & _)|(-> & _)]; split; try lia; intros; lia).
clear Hr1.
aconstsF HJ2 Kgot4 Kcell4 Kguar4 Kuar4.
lazymatch type of HS with st_ok _ _ ?ssx _ => let l := eval vm_compute in (seq 0 (length (ss_mem ssx))) in
reseat HS HJ2 HP2 l AG
ltac:(first [ eapply region_kept_aview; [evalE AG | intros a Ha; apply Hfr2;
[ clear - Ha Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF4096 HFceil HF8lo HF8hi; unfold SB in *; lia
| clear - Ha Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi; ceil; unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, SB in *; lia
| clear - Ha Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi; ceil; unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, SB in *; lia
| clear - Ha Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi; ceil; unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, SB in *; lia ] | exact Hpres2]
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val trbsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot4 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val trbsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell4 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val trbsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar4 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val trbsegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar4 | clear; lia] ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]) end.
unfold w64 in Ha02.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) [10%bv : bv 5]) in
let vals' := eval cbn [map ms_regs restrict] in vals in
pose proof (st_ok_havoc_win trbsegs 360 Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
assert (E360 : ew (havoc Ex 360 vals') 360 = Z_to_bv 64 r1) by (rewrite (ew_havoc_new _ 360 vals' 0 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth]; exact Ha02);
clear HS; rename HS3 into HS;
set_regs_rec HS 360%nat vals' 0%nat [10%bv : bv 5] end.
rebaseE HS AG HEv; clear HEv.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_havoc_win trbsegs 361 Ev ssv msv [Z_to_bv 64 cur1] HS ltac:(vm_compute; reflexivity)) as HS3;
assert (E361 : ew (havoc Ev 361 [Z_to_bv 64 cur1]) 361 = Z_to_bv 64 cur1) by (exact (ew_havoc_new _ 361 [Z_to_bv 64 cur1] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
clear HS; rename HS3 into HS end.
rebaseE HS AG HEv; clear HEv.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
lazymatch type of HS with st_ok _ ?Ev2 _ _ =>
pose proof (ast_ok_add_region trbsegs Ev2 _ _ (YQ0b.mkRegion (Some 70%nat) 48 56 48 56 [YQ0b.mkChunk 48 (CVal 8 (SOff 361 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
evalE AG; split; [clear - Hsp1 Hceil Hslo Hstk0 FFS C1; lia|]; split; [clear - Hsp1 Hshi H47; lia|]; split;
[ intros o Ho; apply (apresent_writable trbsegs); apply HJpres; rewrite FFS; clear - Ho Hsp1; lia
| apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val trbsegs Ev2 _ sp1 48 8 (SOff 361 0) cur1); [rewrite sv_denot_SOff0; exact E361 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Hcb1 Hn26; lia | clear; cbn; lia
| replace (sp1 + 48) with (sp1 + 32 + 16) by (clear; lia); exact Vc'] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; evalE AG;
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi HFq HF8 HF8c; unfold SB in *; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
clear HJpres.
rt_hand RN HS.
split; [split; [exact Hk0 | split; [cbn [c_ly c_S]; exact Eab3 | exists cur1; cbn [c_n]; split; [exact E361 | exact Hcb1]]]|].
exists r1. cbn [c_n]. split; [exact E360 | exact Hr1v].
Qed.
Lemma rt_B1 : rt_from B ss_B2 (INV_Bn B 361) -> rt_from B ss_B1 (INV_0 B 0).
Proof. exact rt_B1_aux. Qed.
End c.
End b.
