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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCdv YCe9 YCgi YChv YChx YChw YChb YChm YChi YChj YChn YChf YChe.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
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
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Lemma ra_C_aux : ra_from B ss_D (INV_D B) -> ra_from B ss_C (INV_0 B 1).
Proof.
intros RD. ra_prelude.
pose proof HINV as (Hk3 & Eab3).
assert (Hraw3 : In (raw, RAW_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hraw_in).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hing).
ra_blocks3 Hraw3 Hing3. fold F in HdFR, HdFG.
relowC HS AG E10 E11 E32 E10n E11n E32n.
reshok_bx HS 40%nat.
aj_run_tok trbtbl_lib_ok HS HJ3 SHOK RABspan; [awrRA AG fpos F EFA3 |]. clear_frames.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 70%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRfs; cbn [ms_mem restrict] in HRfs;
lazymatch type of HRfs with region_ok _ _ _ (YQ0b.mkRegion (Some 70%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 70 (SB + F / 8) cs lo hi wlo whi 6 1%N (SLit 0) 0 HRfs
ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V6;
pose proof (field_of_region Ex _ 70 (SB + F / 8) cs lo hi wlo whi 7 1%N (SLit 2) 2 HRfs
ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V7 end;
clear HRfs;
pose proof (aview_of_val_mem1 trbsegs _ _ _ _ V6 ltac:(lia)) as Hsh6;
pose proof (aview_of_val_mem1 trbsegs _ _ _ _ V7 ltac:(lia)) as Hsh7;
assert (HRA3 : range_addressable (aview trbsegs (w_H W3) (ms_mem msX)) SHADOW_OFF (F + 49) 9);
[ eapply (range_addressable_sub _ _ (F + 48) 10); [|lia|lia];
change 10 with (8 + 2); apply range_addressable_app; [lia| |];
[ apply range_addressable_zero8; [|rewrite HFq; replace (32 * (F / 32) + 48) with ((4 * (F / 32) + 6) * 8) by lia; apply Z_mod_mult];
rewrite <- Hsh6; unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF; f_equal; rewrite HFq at 1; rewrite HF8;
replace (32 * (F / 32) + 48) with ((4 * (F / 32) + 6) * 8) by lia; rewrite Z.div_mul by lia; lia
| eapply (range_addressable_partial _ SHADOW_OFF (F + 48 + 8) 2); [|rewrite HFq; replace (32 * (F / 32) + 48 + 8) with ((4 * (F / 32) + 7) * 8) by lia; apply Z_mod_mult|lia];
rewrite <- Hsh7; unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF; f_equal; rewrite HFq at 1; rewrite HF8;
replace (32 * (F / 32) + 48 + 8) with ((4 * (F / 32) + 7) * 8) by lia; rewrite Z.div_mul by lia; lia ]
| ] end.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 337168) with (Z_to_bv 64 A_asan_memset).
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3. aconstsA HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_at trbsegs B LAWS Hsegs OSet A_asan_memset AMEMSET _ (ms_regs msX) (ms_mem msX) TRAWADD_STK (spZ regs) [(raw + 40, raw + 44)] ly S W mem md [(1, fpos)]
ly3 S3 _ _ (F + 49) 0 9 (-320) (Z_to_bv 64 0x89784) HJ3) end.
- rewrite Ra0. evalE AG.
- rewrite Ra1. reflexivity.
- rewrite Ra2. reflexivity.
- lia. - lia. - lia.
- unfold spZ at 1. rewrite Rsp. evalE AG.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- intros a Ha. split; [| unfold ESTACK; lia]. right. right. right. exists 1, fpos. split; [left; reflexivity|]. left.
unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. rewrite EFA3. fold F. lia.
- apply amem_range_high; zone_lia.
- exact HRA3.
- intros _. eapply (shadow_hull_vis_of_frame trbsegs B LAWS ly3 S3 _ _ _ 1 fpos (F + 49) 9 (proj1 HJ3) Hfin3);
[rewrite EFA3; fold F; lia | rewrite EFA3; fold F; change (fs_frame_bytes 1) with 128; lia | lia].
- exact I. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff & Hfr4 & Hpres4).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp V6 V7 Hsh6 Hsh7 HRA3.
aconstsA HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos (proj1 HJ4) Hfin3) as (_ & _ & HFpres4 & HFSpres4). change (fs_frame_bytes 1) with 128 in HFpres4, HFSpres4.
change (128 / 8) with 16 in HFSpres4. rewrite !EFA3 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
reseat HS HJ4 HP4 [0; 1; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12]%nat AG
ltac:(idtac; first [ keptIA Hfr4 Hpres4 AG Kgot3 Kgot4 Kcell3 Kcell4 Kguar3 Kguar4 Kuar3 Kuar4 Vgr3 Vgr4
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
assert (Z49 : val_mem trbsegs (mrestrict (w_H W3) mem4) (F + 49) 8 0).
{ apply val_mem_zero8. intros i Hi. replace (F + 49 + i) with (F + 49 + i) by lia. rewrite (Heff i ltac:(lia)). reflexivity. }
assert (Z57 : val_mem trbsegs (mrestrict (w_H W3) mem4) (F + 57) 1 0).
{ intros j Hj. destruct j; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
destruct (aview_byte trbsegs (w_H W3) mem4 (F + 57) 0 ltac:(replace (F + 57) with (F + 49 + 8) by lia; rewrite (Heff 8 ltac:(lia)); reflexivity)) as (b & Hb & Hv & _).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YP0g.le_byte, bv_wrap.
repeat (rewrite Z.shiftr_0_l || rewrite Z.mod_0_l by (vm_compute; discriminate)). lia. }
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region trbsegs Ev _ _ (YQ0b.mkRegion (Some 57%nat) 49 58 49 58
[YQ0b.mkChunk 49 (CVal 8 (SLit 0)); YQ0b.mkChunk 57 (CVal 1 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (HFpres4 (F + o) ltac:(lia)))
| apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ F 49 8 _ 0); [reflexivity | zside | zside | exact Z49]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ F 57 1 _ 0); [reflexivity | zside | zside | exact Z57]|];
apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; unbox; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite RF; evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rawadd, CGIF_SIZE; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. relowC HS AG E10 E11 E32 E10n E11n E32n. reshok_bx HS 40%nat. clear_frames.
aj_run_tok trbtbl_lib_ok HS HJ4 SHOK RABspan; [awrRA AG fpos F EFA3 |]. clear_frames.
srr_branch_tok trbtbl_lib_ok HS SHOK RABspan.
-
unfold branch_taken in Hc. rewrite bv_eqb_unsigned in Hc. cbn [sv_denot] in Hc.
rewrite E49, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.eqb_eq in Hc.
aj_run_to_tok trbtbl_lib_ok HS HJ4 SHOK RABspan 0x89850.
all: try (obl_blk HJ4 E10n E40 Hraw3). all: try (oblFA HJ4 E11n E40 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
1: awrRA AG fpos F EFA3.
clear_frames.
rreg HS (12%bv : bv 5) Qa2. rewrite E37 in Qa2.
lazymatch type of HS with st_ok _ ?Ev _ _ => assert (HvK : sv_denot Ev (SLit 0) = Z_to_bv 64 0) by reflexivity end.
ra_rechunk HS 199%nat 0 4%nat 0%nat HvK Ek199. clear HvK.
rebaseE HS AG HEv. clear HEv.
ra_join HS ss_D 200%nat ra_deads_D
ltac:(idtac;
ra_join_val HS 200%nat 1%nat Qa2 EnC;
lazymatch type of HS with st_ok _ ?Ef _ _ => assert (EK1 : ew Ef 199 = Z_to_bv 64 0) by (rewrite ew_havoc_old by (cbn; lia); exact Ek199) end;
ra_join_fact HS 201%nat (mkAF 0 256 0) ltac:(rewrite EnC, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; clear - Hsg Rsgct; lia);
ra_join_fact HS 199%nat (mkAF 0 8 0) ltac:(rewrite EK1, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; clear; lia)).
ra_hand RD HS. split; [exact Hk3|]. split; [exact Eab3|]. exists 0. split; [exact EK1|]. split; [lia|]. intros Hne. exfalso. apply Hne. exact Hc.
-
unfold branch_taken in Hc. rewrite bv_eqb_unsigned in Hc. cbn [sv_denot] in Hc.
rewrite E49, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.eqb_neq in Hc.
fact_of HS 49%nat F49. rewrite E49, unsigned_lit_small in F49 by lia.
aj_run_to_tok trbtbl_lib_ok HS HJ4 SHOK RABspan 0x897c0; [awrRA AG fpos F EFA3|]. clear_frames.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (14%bv : bv 5) Ra4.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (ra_pow2a B LAWS 9 0 slct W3 (ms_regs msX) (ms_mem msX) _ TRAWADD_STK (spZ regs) [(raw + 40, raw + 44)] ly S W mem md [(1, fpos)] ly3 S3 k eq_refl HJ4);
[ exact Ra0 | exact Ra1 | exact Ra2 | rewrite Ra4; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E49
| clear; lia | clear - Hc Rslct F49; lia | change (2 ^ 0) with 1; clear - Hc Rslct; lia ] end. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & K & -> & HJ5 & HK10 & HK13 & HKlo & HKs1 & HKs2 & Hav5 & Hpr5 & Hrg5).
clear Ra0 Ra1 Ra2 Ra4.
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K 0 (SOff 32 0) [] ssx) in
jafter_stretch HS kk regs5 (mrestrict (w_H W3) mem5) POW_CLOB_RA 0x897d4 HS2;
specialize (HS2 Hrg5 (regions_kept_all Ev (w_H W3) (ms_mem msX) mem5 _ Hav5 Hpr5)) end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (E87 : ew Ev 87 = Z_to_bv 64 K) by (rewrite HEv; unfold POW_CLOB_RA; cbn [map]; rewrite (ew_havoc_new _ 87 _ 0 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth]; exact HK10) end.
clear HEv.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (st_ok_add_fact trbsegs Ev _ _ 87 (mkAF 0 8 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E87, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; clear - HKlo; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. relowC HS AG E10 E11 E32 E10n E11n E32n. reshok_bx HS 40%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ5 SHOK RABspan 0x89850.
all: try (oblFA HJ5 E11n E40 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
1: awrRA AG fpos F EFA3.
clear_frames.
rreg HS (12%bv : bv 5) Qa2. rewrite E49 in Qa2.
lazymatch type of HS with st_ok _ ?Ev _ _ => pose proof (denot_K1b Ev 87 K E87 ltac:(clear - HKlo; lia)) as HvK end.
ra_rechunk HS 199%nat (Z.max K 1) 4%nat 0%nat HvK Ek199. clear HvK.
rebaseE HS AG HEv. clear HEv.
ra_join HS ss_D 200%nat ra_deads_D
ltac:(idtac;
ra_join_val HS 200%nat 1%nat Qa2 EnC;
lazymatch type of HS with st_ok _ ?Ef _ _ => assert (EK1 : ew Ef 199 = Z_to_bv 64 (Z.max K 1)) by (rewrite ew_havoc_old by (cbn; lia); exact Ek199) end;
ra_join_fact HS 201%nat (mkAF 0 256 0) ltac:(rewrite EnC, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; clear - F49; lia);
ra_join_fact HS 199%nat (mkAF 0 8 0) ltac:(rewrite EK1, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; clear - HKlo; lia)).
ra_hand RD HS. split; [exact Hk3|]. split; [exact Eab3|]. exists (Z.max K 1). split; [exact EK1|]. split; [clear - HKlo; lia|].
intros _. clear - HKs1 HKlo. destruct (Z_le_gt_dec K 0) as [Hk0 | Hk0].
+ replace (2 ^ K) with 1 in HKs1 by (replace K with 0 by lia; reflexivity).
replace (Z.max K 1) with 1 by lia. change (2 ^ 1) with 2. lia.
+ replace (Z.max K 1) with K by lia. lia.
Qed.
Lemma ra_C : ra_from B ss_D (INV_D B) -> ra_from B ss_C (INV_0 B 1).
Proof. exact ra_C_aux. Qed.
End d.
End c.
