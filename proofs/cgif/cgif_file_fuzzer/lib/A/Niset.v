(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI08 YI0t YI0m YI0n YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCbw YCbx.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC81 YC4b YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a AC93 AC9g AC95 AC91 AC99 AC92 AC9b AC9c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
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
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Lemma tisetup_seg : forall cx lyc Sc W memc mdc ly7 S7 W7 (regs : bvmap 5 word) memT mdT (regs0 : bvmap 5 word) X q,
acx_ok cx -> acx_ranges cx -> acx_seps cx -> acx_blk (ablocks B ly7 S7) cx ->
ajournal SEGS B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 memT mdT 7 ->
alzw_regs_core regs cx -> agen_at (mrestrict (w_H W7) memT) cx (la_lp X) (la_dp X) (la_mp X) ->
alzw_slots (mrestrict (w_H W7) memT) cx -> alzw_sslots (mrestrict (w_H W7) memT) cx -> tlzw_frame (mrestrict (w_H W7) memT) (z_sp cx) regs0 ->
lzw_inv (z_idl cx) (z_nP cx) X ->
getr regs 23 = w64 (la_s X + 1) -> getr regs 15 = w64 q -> getr regs 7 = w64 (z_ti cx) -> getr regs 13 = w64 (z_img cx) ->
getr regs 16 = w64 (z_nP cx - 1) -> 0 <= q < 4096 -> la_s X + 1 < z_nP cx - 1 ->
SRr SEGS W7 (mkCfg (mkst regs (Z_to_bv 64 (BASE + PC_ISET)) memT (seg_rom SEGS)) mdT)
(fun W' c' => W' = W7 /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + PC_INNER)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 mem' md' 7 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (z_sp cx - 320 + 8 <= a < z_sp cx - 320 + 56) ->
mbyte SEGS (mrestrict (w_H W7) mem') a = mbyte SEGS (mrestrict (w_H W7) memT) a) /\
val_mem SEGS (mrestrict (w_H W7) mem') (z_sp cx - 320 + 48) 8 (z_ti cx) /\
alzw_regs_core regs' cx /\ tin_pre cx regs' (la_s X + 2) q).
Proof.
intros cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X q HCX HRG HSEP (HBg & HBi & HBt) HJ HFC HG HSL HSS HFR HI H23 H15 H7 H13 H16 Hq Hs.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HJ as (HAR & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 336 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
pose proof HCX as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR0 & HpR47 & HpR8 & Hgp & Htp & EMR).
pose proof HRG as (HR & Hbi0 & Hbi1 & Hbi2 & Hbi3). cbn [ranges acx_tabs lzw_tabs app] in HR.
destruct HR as ((Rld1 & Rld2 & Rld3 & Rld4) & (Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rg1 & Rg2 & Rg3 & _) & _).
pose proof (req_size_pos (z_Li cx)) as HrLi.
assert (Hsws : forall a, z_sp cx - 320 <= a < z_sp cx -> apresent (w_H W7) memT a).
{ intros a Ha. apply (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ ltac:(left; rewrite HTS, Has; lia))). }
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
remember (Eimg (Ereg regs (acx_extra cx lp dp mp regs0 ++ more))) as E eqn:HE0. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HE60 : ew E 60 = Z_to_bv 64 (z_img cx + (s + 1))) by (rewrite HE0, <- (Nat.add_0_r 60), (AE_more regs _ _ _ _ _ more 0 ltac:(unfold A_TEXT; lia)), Hmore; reflexivity).
pose proof (AE_sp regs cx lp dp mp regs0 more HFC) as HE2. pose proof (AE_ctx regs cx lp dp mp regs0 more HFC) as HE8.
pose proof (AE_SB regs cx lp dp mp regs0 more HFC) as HE27. pose proof (AE_idl regs cx lp dp mp regs0 more HFC) as HE25.
pose proof (AE_ti regs cx lp dp mp regs0 more) as HE53. pose proof (AE_nP regs cx lp dp mp regs0 more) as HE59.
pose proof (AE_img regs cx lp dp mp regs0 more) as HE32.
rewrite <- HE0 in HE2, HE8, HE27, HE25, HE53, HE59, HE32.
assert (HE23 : ew E 23 = Z_to_bv 64 (s + 1)) by (rewrite HE0, (AE_reg regs _ _ _ _ _ more 23%bv 23) by reflexivity; exact H23).
assert (HE15 : ew E 15 = Z_to_bv 64 q) by (rewrite HE0, (AE_reg regs _ _ _ _ _ more 15%bv 15) by reflexivity; exact H15).
assert (HE16 : ew E 16 = Z_to_bv 64 (z_nP cx - 1)) by (rewrite HE0, (AE_reg regs _ _ _ _ _ more 16%bv 16) by reflexivity; exact H16).
assert (HS1 : st_ok_pi SEGS VAL E (alzw_ss PC_ISET asr_fix false true []
[ (23%nat, mkAF 1 99999998 0); (15%nat, mkAF 0 4095 0); (16%nat, mkAF 0 99999999 0); (60%nat, APTR 0) ] []
[ (SAlu ALU_ADD (SOff 32 0) (SOff 23 0), SOff 60 0) ])
(mkst regs (Z_to_bv 64 (BASE + PC_ISET)) m (seg_rom SEGS))).
{ rewrite HE0. apply (alzw_st_ok cx regs regs0 lp dp mp more m PC_ISET asr_fix false true); rewrite <- ?HE0.
- exact HCX. - exact HRG. - exact HFC. - exact HG. - exact HSL. - exact HSS. - exact HFR.
- intros X0; discriminate X0.
- intros _ a Ha. apply (apresent_writable SEGS). apply Hsws. lia.
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
pose proof (ast_ok_set_reg E _ (mkst regs (Z_to_bv 64 (BASE + PC_ISET)) m (seg_rom SEGS)) 7%bv (SOff 53 0) HS1 eq_refl
ltac:(cbn [sv_denot ms_regs mkst]; rewrite HE53, Z.add_0_r, unsigned_lit_small by lia; symmetry; exact H7)) as HS2.
pose proof (ast_ok_set_reg E _ (mkst regs (Z_to_bv 64 (BASE + PC_ISET)) m (seg_rom SEGS)) 13%bv (SOff 32 0) HS2 eq_refl
ltac:(cbn [sv_denot ms_regs mkst]; rewrite HE32, Z.add_0_r, unsigned_lit_small by lia; symmetry; exact H13)) as HS.
clear HS1 HS2. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts alzw_ss] in HS.
change (mkst regs (Z_to_bv 64 (BASE + PC_ISET)) m (seg_rom SEGS)) with (restrict (w_H W7) (mkst regs (Z_to_bv 64 (BASE + PC_ISET)) memT (seg_rom SEGS))) in HS.
shok_auto SHOK (SOff 27 0) E (mrestrict (w_H W7) (ms_mem (mkst regs (Z_to_bv 64 (BASE + PC_ISET)) memT (seg_rom SEGS)))).
change memT with (ms_mem (mkst regs (Z_to_bv 64 (BASE + PC_ISET)) memT (seg_rom SEGS))) in HJ.
paj_run_to_tok RUNTO HS HJ SHOK Bspan PC_INNER.
{ apply awr_ok_cons_ro; [cbn; lia|].
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (-320)); [reflexivity | cbn [ew ewset Nat.eqb]; rewrite HE2; rewrite unsigned_lit_small by lia; lia | cbn; lia | cbn; lia |].
apply awr_ok_nil. }
rewrite (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- exists regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists rg, mm, mdx end.
split; [reflexivity|]. split; [exact HJ|].
split.
{ intros a Ha Hn. eapply (aframe_mbyte_list E _ _ _ [(0, 0); (z_sp cx - 320 + 8, z_sp cx - 320 + 56)] a HFr Ha);
[ repeat (apply Forall2_cons; [first [left; cbn; lia | right; cbn [fst snd YP09.r_base YP09.r_wlo YP09.r_whi astk_region actx_region base_val]; rewrite ?HE2, ?unsigned_lit_small by lia; lia]|]); apply Forall2_nil
| cbn; repeat split; lia ]. }
split.
{ lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx => pose proof (st_ok_pi_region_nth Ex ssx msx 1%nat _ HS eq_refl) as HRg end.
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
End d.
End b.
