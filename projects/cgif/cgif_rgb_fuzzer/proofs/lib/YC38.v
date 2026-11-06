(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI01 YI07 YI03 YI04 YI06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC0x YC3g YC2z YC3e YC31 YC2x YC2v YC35 YC2y YC37.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma U_sub_smallI : forall E a b x y, U E a = x -> U E b = y -> 0 <= y <= x -> x < 2 ^ 64 ->
U E (SAlu ALU_ADD a (SMd M_MUL b (SLit (-1)))) = x - y.
Proof.
intros E a b x y Hx Hy Rxy Rx. rewrite U_SAlu, U_SMd, U_SLit. cbn [zalu_raw zmd_raw]. rewrite Hx, Hy. unfold zcanon.
replace ((-1) mod M64) with (M64 - 1) by reflexivity.
rewrite Zplus_mod_idemp_r. replace (x + y * (M64 - 1)) with (x - y + y * M64) by ring. rewrite Z_mod_plus_full. apply Z.mod_small. unfold M64. lia.
Qed.
Definition ss_tiset : sstate :=
alzw_ss PC_ISET (sr_set (sr_set asr_fix 7%bv (SOff 53 0)) 13%bv (SOff 32 0)) false true []
[ (23%nat, mkAF 1 99999998 0); (15%nat, mkAF 0 4095 0); (16%nat, mkAF 0 99999999 0); (60%nat, APTR 0) ] []
[ (SAlu ALU_ADD (SOff 32 0) (SOff 23 0), SOff 60 0) ].
Section S.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Let HBcode := tl_code B TL.
Lemma tisetup_seg : forall cx lyc Sc W memc mdc ly7 S7 W7 (regs : bvmap 5 word) memT mdT (regs0 : bvmap 5 word) X q,
acx_ok cx -> acx_ranges cx -> acx_seps cx -> acx_blk (ablocks B ly7 S7) cx ->
ajournal trasegs B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 memT mdT 7 ->
alzw_regs_core regs cx -> agen_at (mrestrict (w_H W7) memT) cx (la_lp X) (la_dp X) (la_mp X) ->
alzw_slots (mrestrict (w_H W7) memT) cx -> alzw_sslots (mrestrict (w_H W7) memT) cx -> tlzw_frame (mrestrict (w_H W7) memT) (z_sp cx) regs0 ->
lzw_inv (z_idl cx) (z_nP cx) X ->
getr regs 23 = w64 (la_s X + 1) -> getr regs 15 = w64 q -> getr regs 7 = w64 (z_ti cx) -> getr regs 13 = w64 (z_img cx) ->
getr regs 16 = w64 (z_nP cx - 1) -> 0 <= q < 4096 -> la_s X + 1 < z_nP cx - 1 ->
SRr trasegs W7 (mkCfg (mkst regs (Z_to_bv 64 PC_ISET) memT (seg_rom trasegs)) mdT)
(fun W' c' => W' = W7 /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 PC_INNER) mem' (seg_rom trasegs)) md' /\
ajournal trasegs B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 mem' md' 7 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (z_sp cx - 320 + 8 <= a < z_sp cx - 320 + 56) ->
mbyte trasegs (mrestrict (w_H W7) mem') a = mbyte trasegs (mrestrict (w_H W7) memT) a) /\
val_mem trasegs (mrestrict (w_H W7) mem') (z_sp cx - 320 + 48) 8 (z_ti cx) /\
alzw_regs_core regs' cx /\ tin_pre cx regs' (la_s X + 2) q).
Proof.
intros cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X q HCX HRG HSEP (HBg & HBi & HBt) HJ HFC HG HSL HSS HFR HI H23 H15 H7 H13 H16 Hq Hs.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HJ as (HAR & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 336 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
pose proof HCX as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR0 & HpR47 & HpR8 & Hgp & Htp & EMR).
pose proof HRG as (HR & Hbi0 & Hbi1 & Hbi2 & Hbi3). cbn [ranges acx_tabs lzw_tabs app] in HR.
destruct HR as ((Rld1 & Rld2 & Rld3 & Rld4) & (Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rg1 & Rg2 & Rg3 & _) & _).
pose proof (req_size_pos (z_Li cx)) as HrLi.
assert (Hsws : forall a, z_sp cx - 320 <= a < z_sp cx -> apresent (w_H W7) memT a).
{ intros a Ha. apply (proj1 (awr_byte_present trasegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ ltac:(left; rewrite HTS, Has; lia))). }
rewrite ?C1, ?C2, ?C3, ?C4, ?HTS, ?Has in *. clear C2 C3 C4 HTS Has.
destruct X as [TI LM LI TM s lp dp mp Cn R]. cbn [la_TI la_LM la_LI la_TM la_s la_lp la_dp la_mp] in *.
pose proof HI as (LenTI & LenLM & LenLI & LenTM & BTI & BLI & BLM & UTM & ATMrows & Hdp & Hmp & HA & HR0 & HRC & HCn & Hlp & Hs0).
pose proof (countA_nonneg LI LM) as HA0.
assert (HMRle : z_MR cx <= 26055).
{ assert (z_MR cx * 3838 <= z_MR cx * (4094 - z_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
pose proof (lp_head_bound (z_idl cx) (z_nP cx) (z_MR cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(unfold lzw_par; lia) HI ltac:(cbn [la_s]; lia)) as Hlpb.
cbn [la_lp] in Hlpb. unfold cap in Hlpb.
set (m := mrestrict (w_H W7) memT) in *.
remember [Z_to_bv 64 (z_img cx + (s + 1))] as more eqn:Hmore.
remember (Ereg regs (acx_extra cx lp dp mp regs0 ++ more)) as E eqn:HE0.
assert (HE60 : ew E 60 = Z_to_bv 64 (z_img cx + (s + 1))) by (rewrite HE0, <- (Nat.add_0_r 60), (AE_more regs _ _ _ _ _ more 0), Hmore; reflexivity).
pose proof (AE_sp regs cx lp dp mp regs0 more HFC) as HE2. pose proof (AE_ctx regs cx lp dp mp regs0 more HFC) as HE8.
pose proof (AE_SB regs cx lp dp mp regs0 more HFC) as HE27. pose proof (AE_idl regs cx lp dp mp regs0 more HFC) as HE25.
pose proof (AE_ti regs cx lp dp mp regs0 more) as HE53. pose proof (AE_nP regs cx lp dp mp regs0 more) as HE59.
pose proof (AE_img regs cx lp dp mp regs0 more) as HE32.
rewrite <- HE0 in HE2, HE8, HE27, HE25, HE53, HE59, HE32.
assert (HE23 : ew E 23 = Z_to_bv 64 (s + 1)) by (rewrite HE0, (AE_reg regs _ _ _ _ _ more 23%bv 23) by reflexivity; exact H23).
assert (HE15 : ew E 15 = Z_to_bv 64 q) by (rewrite HE0, (AE_reg regs _ _ _ _ _ more 15%bv 15) by reflexivity; exact H15).
assert (HE16 : ew E 16 = Z_to_bv 64 (z_nP cx - 1)) by (rewrite HE0, (AE_reg regs _ _ _ _ _ more 16%bv 16) by reflexivity; exact H16).
assert (HS1 : st_ok trasegs E (alzw_ss PC_ISET asr_fix false true []
[ (23%nat, mkAF 1 99999998 0); (15%nat, mkAF 0 4095 0); (16%nat, mkAF 0 99999999 0); (60%nat, APTR 0) ] []
[ (SAlu ALU_ADD (SOff 32 0) (SOff 23 0), SOff 60 0) ])
(mkst regs (Z_to_bv 64 PC_ISET) m (seg_rom trasegs))).
{ rewrite HE0. apply (alzw_st_ok cx regs regs0 lp dp mp more m PC_ISET asr_fix false true); rewrite <- ?HE0.
- exact HCX. - exact HRG. - exact HFC. - exact HG. - exact HSL. - exact HSS. - exact HFR.
- intros X0; discriminate X0.
- intros _ a Ha. apply (apresent_writable trasegs). apply Hsws. lia.
- lia. - lia. - lia.
- rewrite HE0. apply (regs_ok_fix regs cx); [exact HFC | lia | lia].
- vm_compute; reflexivity.
- constructor.
- exact I.
- exact I.
- exact I.
- cbn [atoms_ok]. unfold afact_ok, APTR. cbn [af_lo af_hi af_al2].
rewrite HE23, HE15, HE16, HE60, !unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; lia.
- exact I.
- cbn [alias_ok]. split; [| exact I]. apply (alias_add E 32 23 60 (z_img cx) (s + 1) HE32 HE23 HE60); lia. }
pose proof (ast_ok_set_reg E _ (mkst regs (Z_to_bv 64 PC_ISET) m (seg_rom trasegs)) 7%bv (SOff 53 0) HS1 eq_refl
ltac:(cbn [sv_denot ms_regs mkst]; rewrite HE53, Z.add_0_r, unsigned_lit_small by lia; symmetry; exact H7)) as HS2.
pose proof (ast_ok_set_reg E _ (mkst regs (Z_to_bv 64 PC_ISET) m (seg_rom trasegs)) 13%bv (SOff 32 0) HS2 eq_refl
ltac:(cbn [sv_denot ms_regs mkst]; rewrite HE32, Z.add_0_r, unsigned_lit_small by lia; symmetry; exact H13)) as HS.
clear HS1 HS2. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts alzw_ss] in HS.
change (mkst regs (Z_to_bv 64 PC_ISET) m (seg_rom trasegs)) with (restrict (w_H W7) (mkst regs (Z_to_bv 64 PC_ISET) memT (seg_rom trasegs))) in HS.
shok_auto SHOK (SOff 27 0) E (mrestrict (w_H W7) (ms_mem (mkst regs (Z_to_bv 64 PC_ISET) memT (seg_rom trasegs)))).
change memT with (ms_mem (mkst regs (Z_to_bv 64 PC_ISET) memT (seg_rom trasegs))) in HJ.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK Bspan PC_INNER.
{ apply awr_ok_cons_ro; [cbn; lia|].
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (-320)); [reflexivity | cbn [ew ewset Nat.eqb]; rewrite HE2; rewrite unsigned_lit_small by lia; lia | cbn; lia | cbn; lia |].
apply awr_ok_nil. }
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- exists regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists rg, mm, mdx end.
split; [reflexivity|]. split; [exact HJ|].
split.
{ intros a Ha Hn. eapply (aframe_mbyte_list E _ _ _ [(0, 0); (z_sp cx - 320 + 8, z_sp cx - 320 + 56)] a HFr Ha);
[ repeat (apply Forall2_cons; [first [left; cbn; lia | right; cbn [fst snd YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi astk_region actx_region base_val]; rewrite ?HE2, ?unsigned_lit_small by lia; lia]|]); apply Forall2_nil
| cbn; repeat split; lia ]. }
split.
{ lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx => pose proof (st_ok_region_nth Ex ssx msx 1%nat _ HS eq_refl) as HRg end.
cbn [ms_mem restrict] in HRg.
change 8%nat with (N.to_nat 8). eapply (field_of_region _ _ 2%nat (z_sp cx - 320) _ _ _ _ _ 48 8%N _ (z_ti cx) HRg);
[ cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite HE2; apply unsigned_lit_small; lia | cbn; tauto
| cbn [sv_denot ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite HE53, Z.add_0_r, unsigned_lit_small by lia; reflexivity
| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia ]. }
split.
{ eapply (alzw_regs_core_after _ _ _ _ _ _ _ HS); [vm_compute; reflexivity | intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | exact HE0 | exact HFC | lia | lia]. }
unfold tin_pre.
repeat match goal with |- _ /\ _ => split end.
- aregv HS (23%bv : bv 5).
- aregv HS (15%bv : bv 5).
- aregv HS (11%bv : bv 5).
- aregv HS (17%bv : bv 5).
- rregU HS (28%bv : bv 5) (z_nP cx - 1 - (s + 1))
ltac:(apply (U_sub_smallI _ (SOff 16 0) (SOff 23 0));
[ apply U_atom; [cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; assumption | lia]
| apply U_atom; [cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; assumption | lia] | lia | lia ]) R28.
rewrite R28. unfold w64. f_equal. lia.
- aregv HS (16%bv : bv 5).
Qed.
End S.
End c.
