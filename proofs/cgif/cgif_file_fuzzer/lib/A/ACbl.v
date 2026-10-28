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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI08 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC81 YC4b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbk.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC85.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Definition WCBF_RET : Z := 0x660.
Section f.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Variable K : asink_syms.
Hypothesis AIL : asink_img_laws SEGS B K.
Hypothesis AFWRITE : afwrite_spec SEGS B K (SIGMA AS_fwrite).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Definition BxF : sv := SOff 33 0.
Definition wcbF_regions : smem :=
[ stack_region 16; got_regionP; bcell_regionP 33;
YP09.mkRegion (Some 10%nat) 0 CGIF_OBJ 0 0 [YP09.mkChunk 80 (CVal 8 (SOff 32 0))] ].
Definition wcbF_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 4096 140737479966720 4); (32%nat, mkAF 4096 140737479966720 0); (33%nat, mkAF SB SB 0) ] [] [].
Definition ss_wcbF : sstate := mkSS A_cgif_writecb sr_atoms wcbF_regions None wcbF_facts.
Definition wcbF_SH : list shent := [ mkSHE 10 0 CGIF_OBJ ].
Definition BspanF : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition wcbF_extra (pf : Z) : list word := map (Z_to_bv 64) [pf; SB].
Lemma wcbF_entry : forall W ly S regs mem md ch g pf,
afn_pre SEGS B WCBF_STK ly S W regs mem md ch ->
getr regs 10 = w64 g ->
In (g, CGIF_OBJ) (ablocks B ly S) ->
val_mem SEGS (mrestrict (w_H W) mem) (g + 80) 8 pf ->
In (pf, FILE_BLOCK) (ablocks B ly S) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (wcbF_extra pf))) ss_wcbF
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_cgif_writecbP) mem (seg_rom SEGS)))
/\ sh_ok SEGS BxF wcbF_SH (Eimg (Ereg regs (wcbF_extra pf))) (mrestrict (w_H W) mem).
Proof.
intros W ly S regs mem md ch g pf HPRE H10 Hing Mfile Hinf.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : WCBF_STK = 16 + AFWRITE_STK) by reflexivity. assert (FS : AFWRITE_STK = 6352) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md g CGIF_OBJ HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_OBJ HAR Hing) as Hgh_img.
change (req_size CGIF_OBJ) with 96 in *.
destruct (al_blocks _ _ LAWS ly S W mem md pf FILE_BLOCK HAR Hinf) as (Hf16 & Hf4096 & Hfceil & _).
change (req_size FILE_BLOCK) with 1264 in *.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (wcbF_extra pf))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 g) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 pf) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_wcbF, A_cgif_writecbP, A_cgif_writecb. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold wcbF_regions, stack_region, got_regionP, bcell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 BxF SB);
[cbn [sv_denot BxF]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* rewrite (VB 10%nat g E10) by lia. unfold CGIF_OBJ. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ g 80 8 _ pf); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mfile].
+ apply pairwise_disjoint_of_extents. unfold wcbF_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat g E10) by lia. rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). cbn [base_val]. rewrite Usp.
unfold CGIF_OBJ.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hgceil Hgh Hgh_img Hg4096 C1 C3 WS FS Hstk0 HcellR HgcD HgotR. clear. unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [wcbF_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, E33, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hgceil Hgh Hgh_img Hg4096 Hg16 Hf4096 Hfceil Hal16 C1 C3 WS FS Hstk0. clear. unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, wcbF_SH. constructor; [|constructor].
apply (shent_ok_of_block SEGS B LAWS ly S W mem md E BxF 10 g CGIF_OBJ 0 CGIF_OBJ HAR Hing).
+ unfold U, BxF. cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia.
+ change (req_size CGIF_OBJ) with 96. unfold CGIF_OBJ. lia.
Qed.
Theorem pb_wcbF : twcbF_spec SEGS K B A_cgif_writecbP.
Proof.
unfold twcbF_spec.
intros W ly S regs mem md ch g p n pf Sg bs HPRE H10 H11 H12 Hing Mfile Hinf HSINK GSRC Hn Hn1 HSmax HSf HSstk Hp0 HSam HSra HShull.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (wcbF_entry W ly S regs mem md ch g pf HPRE H10 Hing Mfile Hinf) as [HS SHOK].
pose proof (ajournal_init SEGS B WCBF_STK (asink_fp pf) ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : WCBF_STK = 16 + AFWRITE_STK) by reflexivity. assert (FS : AFWRITE_STK = 6352) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md g CGIF_OBJ HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
destruct (al_blocks _ _ LAWS ly S W mem md pf FILE_BLOCK HAR Hinf) as (Hf16 & Hf4096 & Hfceil & _).
change (req_size CGIF_OBJ) with 96 in *. change (req_size FILE_BLOCK) with 1264 in *.
remember (Eimg (Ereg regs (wcbF_extra pf))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 g) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 p) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 pf) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (wcbF_extra pf)) E) by (rewrite HE; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
unfold cfg_at. change (w64 A_cgif_writecbP) with (Z_to_bv 64 A_cgif_writecbP). unfold A_cgif_writecbP, A_cgif_writecb.
paj_run_tok RUN HS HJ SHOK BspanF. { awr_ok_tac. exact Usp. }
idtac "WCBF RUN1 OK".
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 16 <= a < spZ regs) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; lia|]); destruct Hin)) as UN.
pmkst HS.
prreg HS (2%bv : bv 5) Q2. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (1%bv : bv 5) Q1. prreg HS (8%bv : bv 5) Q8.
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR. unfold YG0f.ASAN_CEIL in CR.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
assert (HSINK1 : asink_at SEGS K (mrestrict (w_H W) mm) mdq pf Sg) end.
{ apply (asink_at_model SEGS K _ md); [reflexivity | reflexivity |].
apply (asink_at_frame SEGS K (mrestrict (w_H W) mem)); [|exact HSINK].
intros a Ha. apply (mbyte_of_aview SEGS). unfold FILE_BLOCK in Ha.
destruct Ha as [Ha | Ha]; [| pose proof (proj1 (ail_env _ _ _ AIL a Ha)) as Hi; pose proof (Hsegs a Hi) as Hlo; unfold kLowMemEnd in Hlo];
(apply UN; [lia | lia]). }
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
assert (GSRC1 : garr8 SEGS (mrestrict (w_H W) mm) p bs);
[ eapply garr8_frame; [exact GSRC|]; intros a Ha; apply (mbyte_of_aview SEGS); rewrite <- Hn in Ha; unfold WCBF_STK, YC20.WCB_STK, AFWRITE_STK in HSstk;
apply UN; [unfold amem_range in HSam; lia | lia] |];
assert (HSra1 : range_addressable (aview SEGS (w_H W) mm) SHADOW_OFF p n);
[ eapply (range_addressable_kept_win _ _ (spZ regs - 16) (spZ regs)); [exact UN | unfold kHighShadowEnd; lia | exact Hp0 | unfold amem_range in HSam; lia | exact HSra] |];
assert (HShull1 : shadow_hull_vis (aview SEGS (w_H W) mm) p n);
[ eapply (shadow_hull_vis_kept_win _ _ (spZ regs - 16) (spZ regs)); [exact UN | unfold kHighShadowEnd; lia | exact Hp0 | unfold amem_range in HSam; lia | lia | exact HShull] |];
assert (Qsp : spZ rg = spZ regs + -16) by (unfold spZ in *; rewrite Q2, Usp; apply unsigned_lit_small; lia)
end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_bind;
[ eapply (cl_callS B LAWS W rg mm _ WCBF_STK (spZ regs) (asink_fp pf) ly S W mem md [] ly S mdq 0 AFWRITE_STK (asink_fp pf) 0 (-16)
(Z_to_bv 64 (BASE + WCBF_RET)) []
(fun ly2 S2 W2 regs2 mem2 md2 => ly2 = ly /\ S2 = S /\ getr regs2 10 = w64 n /\ asink_at SEGS K (mrestrict (w_H W2) mem2) md2 pf (Sg ++ bs)) HJ Qsp);
[ reflexivity | lia | rewrite FS; lia | rewrite WS; lia
| rewrite Q3, E3; exact Hgp | rewrite Q4, E4; exact Htp
| exact Q1 | apply ret_ok_codeptr_v; [unfold WCBF_RET; lia | reflexivity] | unfold WCBF_RET; rewrite unsigned_lit_small by lia; lia
| apply achain_low; unfold s0Z; rewrite Q8, E12, unsigned_lit_small by lia; lia
| intros HPRE1; eapply SRr_mono;
[ eapply (AFWRITE W ly S rg mm mdq [] p n pf Sg bs HPRE1);
[ rewrite Q10, E11; reflexivity | exact Q11 | rewrite Q12, E12; reflexivity | rewrite Q13, E32; reflexivity
| exact Hinf | exact HSINK1 | exact GSRC1 | exact Hn | exact Hn1 | exact HSmax | exact HSf
| rewrite Qsp; unfold WCBF_STK, YC20.WCB_STK in HSstk; lia | exact Hp0 | exact HSam | exact HSra1 | exact HShull1 ]
| cbv beta; intros W2 c2 _ (regs2 & mem2 & md2 & -> & HJ1 & HP & Ha0 & HSINK2);
exists ly, S, regs2, mem2, md2; split; [rewrite Q1; reflexivity | split; [exact HJ1 | split; [exact HP | ]]];
split; [reflexivity | split; [reflexivity | split; [exact Ha0 | exact HSINK2]]] ]
| intros a Ha; left; exact Ha ]
| ] end.
clear SHOK. cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 & (-> & -> & Ha0 & HSINK2)).
pose proof (proj1 HJ2) as HAR2.
idtac "WCBF CALL OK".
jafter_call_keep_pi HS 34%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
cbn [ms_mem ms_regs restrict mkst] in HS2, HJc.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ repeat apply Forall_cons; [| apply Forall_nil].
eapply (region_kept_stack_sub SEGS B); [exact HJc | exact HJ2 | exact Usp | lia | rewrite WS; lia | lia | cbn; lia | cbn; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 34 (map (getr regs2) CLOB)) as E2' eqn:HE2' in HS. assert (HEI2p : img_env VAL A_LIM E2') by (rewrite HE2'; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall k, (k < 34)%nat -> ew E2' k = ew E k) by (intros k Hk; rewrite HE2'; apply YN3v.ew_havoc_old; exact Hk).
assert (HAE2 : env_agree 32 (Ereg regs (wcbF_extra pf)) E2') by (rewrite HE2'; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
assert (F38 : ew E2' 38 = Z_to_bv 64 n) by (rewrite HE2'; change 38%nat with (34 + 4)%nat; rewrite (YN3v.ew_havoc_new E 34 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0)) by (cbv; lia); cbn [nth map]; exact Ha0).
clear HE2'.
assert (F1 : ew E2' 1 = getr regs 1) by (rewrite OLD2 by (cbv; lia); exact E1).
assert (F12 : ew E2' 12 = Z_to_bv 64 n) by (rewrite OLD2 by (cbv; lia); exact E12).
assert (Usp2 : bv_unsigned (ew E2' 2) = spZ regs) by (rewrite OLD2 by (cbv; lia); exact Usp).
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
shok_auto SHOK BxF E2' (mrestrict (w_H W2) mem2).
idtac "WCBF RESEAT OK".
clear HF HFr HG UN.
paj_run_tok RUN HS HJ2 SHOK BspanF. { awr_ok_tac. exact Usp2. }
idtac "WCBF RUN2 OK".
prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) R10.
eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. lazymatch goal with |- exists _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists r, m, d end.
split; [cbn [ms_regs]; rewrite R1, F1, Hra; reflexivity|].
split; [|split; [|split]].
- cbn [ms_mem]. apply (ajournal_materialize SEGS B LAWS Hsegs). replace 0 with (0 + 0) by reflexivity. exact HJ2.
- eapply (aregs_preserved_of_st_ok SEGS _ E2' _ _ regs (wcbF_extra pf) HS); [exact HAE2 | vm_compute; reflexivity].
-
cbn [ms_regs]. rewrite R10, F38, F12. unfold w64. apply bv_eq.
rewrite (alu64_unsigned ALU_ADD), (alu64_unsigned ALU_SLTU), (alu64_unsigned ALU_XOR). cbn [zalu_raw].
rewrite Z.lxor_nilpotent. vm_compute. reflexivity.
- cbn [ms_mem]. apply (asink_at_model SEGS K _ md2); [reflexivity | reflexivity |].
lazymatch goal with |- asink_at _ _ (mrestrict _ ?mf) _ _ _ =>
apply (asink_at_frame SEGS K (mrestrict (w_H W2) mem2)); [|exact HSINK2] end.
intros a Ha. apply (mbyte_of_aview SEGS).
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 16 <= a < spZ regs) HFr
ltac:(intros b wlo whi a0 Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp2 in Hrr; lia|]); destruct Hin)) as UN2.
cbn beta in UN2. unfold FILE_BLOCK in Ha.
destruct Ha as [Ha | Ha]; [| pose proof (proj1 (ail_env _ _ _ AIL a Ha)) as Hi; pose proof (Hsegs a Hi) as Hlo; unfold kLowMemEnd in Hlo];
(apply UN2; [lia | lia]).
Qed.
End f.
End e.
End c.
