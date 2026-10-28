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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC81.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition A_cgif_writecb : Z := AF_asan3_cgif_writecb_or_freeCGIF.
Definition A_cgif_writecbP : Z := BASE + A_cgif_writecb.
Section c.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Variable hw : Z.
Hypothesis HW : hw = 0 \/ hwcb_spec SEGS hw.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Lemma hw_range : 0 <= hw < 2 ^ 64 /\ hw mod 2 = 0.
Proof. destruct HW as [-> | (H1 & H2 & _)]; [split; [lia | reflexivity] | exact (conj H1 H2)]. Qed.
Definition Bx : sv := SOff 33 0.
Definition wcb_regions : smem :=
[ stack_region 16; got_regionP; bcell_regionP 33;
YP09.mkRegion (Some 10%nat) 0 CGIF_OBJ 0 0
[YP09.mkChunk 56 (CVal 8 (SOff 34 0)); YP09.mkChunk 64 (CVal 8 (SOff 32 0)); YP09.mkChunk 80 (CVal 8 (SLit 0))] ].
Definition wcb_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 4096 140737479966720 4); (33%nat, mkAF SB SB 0); (34%nat, mkAF 0 (2^64 - 1) 1) ] [] [].
Definition ss_wcb : sstate := mkSS A_cgif_writecb sr_atoms wcb_regions None wcb_facts.
Definition wcb_SH : list shent := [ mkSHE 10 0 CGIF_OBJ ].
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition wcb_extra (ctx : Z) : list word := map (Z_to_bv 64) [ctx; SB; hw].
Lemma wcb_entry : forall W ly S regs mem md ch g ctx,
afn_pre SEGS B WCB_STK ly S W regs mem md ch ->
getr regs 10 = w64 g ->
In (g, CGIF_OBJ) (ablocks B ly S) ->
val_mem SEGS (mrestrict (w_H W) mem) (g + 56) 8 hw ->
val_mem SEGS (mrestrict (w_H W) mem) (g + 64) 8 ctx ->
val_mem SEGS (mrestrict (w_H W) mem) (g + 80) 8 0 ->
0 <= ctx < 2 ^ 64 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (wcb_extra ctx))) ss_wcb
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_cgif_writecbP) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx wcb_SH (Eimg (Ereg regs (wcb_extra ctx))) (mrestrict (w_H W) mem).
Proof.
intros W ly S regs mem md ch g ctx HPRE H10 Hing Mfn Mctx Mfile Rctx.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : WCB_STK = 16) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md g CGIF_OBJ HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_OBJ HAR Hing) as Hgh_img.
change (req_size CGIF_OBJ) with 96 in *.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (wcb_extra ctx))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 g) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 ctx) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 hw) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
pose proof hw_range as [Rhw Ehw].
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_wcb, A_cgif_writecbP, A_cgif_writecb. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold wcb_regions, stack_region, got_regionP, bcell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
* rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 Bx SB);
[cbn [sv_denot Bx]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
* rewrite (VB 10%nat g E10) by lia. unfold CGIF_OBJ. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor]]].
-- apply (chunk_ok_val SEGS E _ g 56 8 _ hw); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mfn].
-- apply (chunk_ok_val SEGS E _ g 64 8 _ ctx); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mctx].
-- apply (chunk_ok_val SEGS E _ g 80 8 _ 0); [reflexivity | zside | zside | exact Mfile].
+ apply pairwise_disjoint_of_extents. unfold wcb_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat g E10) by lia. rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). cbn [base_val]. rewrite Usp.
unfold CGIF_OBJ.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hgceil Hgh Hgh_img Hg4096 C1 C3 WS Hstk0 HcellR HgcD HgotR. clear. unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [wcb_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E33, E34, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
change (2 ^ 1) with 2.
revert Hslo Hshi H47 Hceil Hgceil Hgh Hgh_img Hg4096 Hg16 Hal16 C1 C3 WS Hstk0 Rhw Ehw. clear. unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, wcb_SH. constructor; [|constructor].
apply (shent_ok_of_block SEGS B LAWS ly S W mem md E Bx 10 g CGIF_OBJ 0 CGIF_OBJ HAR Hing).
+ unfold U, Bx. cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia.
+ change (req_size CGIF_OBJ) with 96. unfold CGIF_OBJ. lia.
Qed.
Theorem pb_wcb : twcb_spec SEGS B A_cgif_writecbP hw.
Proof.
intros W ly S regs mem md ch g ctx HPRE H10 Hing Mfn Mctx Mfile Rctx.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof hw_range as [Rhw Ehw].
destruct (wcb_entry W ly S regs mem md ch g ctx HPRE H10 Hing Mfn Mctx Mfile Rctx) as [HS SHOK].
pose proof (ajournal_init SEGS B WCB_STK [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
remember (Eimg (Ereg regs (wcb_extra ctx))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E34 : ew E 34 = Z_to_bv 64 hw) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (wcb_extra ctx)) E) by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
unfold cfg_at. change (w64 A_cgif_writecbP) with (Z_to_bv 64 A_cgif_writecbP). unfold A_cgif_writecbP, A_cgif_writecb.
paj_run_tok RUN HS HJ SHOK Bspan. { awr_ok_tac. exact Usp. }
psrr_branch_tok RUN BR HS SHOK Bspan.
-
paj_run_tok RUN HS HJ SHOK Bspan. { awr_ok_tac. exact Usp. }
prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold wcb_post. lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
split; [|split; [|split]].
+ cbn [ms_mem]. apply (ajournal_materialize SEGS B LAWS Hsegs). exact HJ.
+ eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs (wcb_extra ctx) HS); [exact HAE | vm_compute; reflexivity].
+ cbn [ms_regs]. rewrite R10. reflexivity.
+ apply Permutation_refl.
-
assert (Hhw : hw <> 0).
{ rewrite branch_eq_U, (U_atom E 34 hw E34), U_lit in Hc by lia. intros Hz. rewrite Hz in Hc. discriminate Hc. }
destruct HW as [Hz | (_ & _ & HWS)]; [exfalso; exact (Hhw Hz)|].
paj_run_tok RUN HS HJ SHOK Bspan. { awr_ok_tac. exact Usp. }
prreg HS (6%bv : bv 5) R6. prreg HS (1%bv : bv 5) R1.
lazymatch type of HS with st_ok_pi _ _ _ ?ssj _ =>
let pcj := eval vm_compute in (ss_pc ssj) in
let wj := eval vm_compute in (match plookup asan3_0_tpi pcj with Some (PW x) => x | _ => 0 end) in
eapply (SRr_jr_pi (PL:=PL_asan3_0) W E ssj _ _ _ wj (6%bv : bv 5) hw HS eq_refl);
[ vm_compute; reflexivity
| vm_refl_bv
| rewrite R6, E34; reflexivity | exact Rhw | exact Ehw |]
end.
intros mat1 ms1 -> HS1.
apply HWS. intros mat2 regs' HP' Ha0 Hra1.
unfold wcb_post. lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst _ _ ?m _) ?d = _ /\ _ => exists ly, S, regs', m, d end.
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
split; [|split; [|split; [exact Ha0 | apply Permutation_refl]]].
+ cbn [ms_mem]. apply (ajournal_materialize SEGS B LAWS Hsegs). apply (ajournal_materialize SEGS B LAWS Hsegs). exact HJ.
+ eapply aregs_preserved_trans; [|exact HP'].
eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs (wcb_extra ctx) HS1); [exact HAE | vm_compute; reflexivity].
Qed.
End c.
End b.
End a.
