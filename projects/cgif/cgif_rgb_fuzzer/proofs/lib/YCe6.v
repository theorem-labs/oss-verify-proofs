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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCe5 YCe9.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Ltac hc_bool H tac :=
rewrite ?branch_eq_U, ?branch_ne_U, ?branch_ltu_U, ?branch_geu_U in H;
rewrite ?U_and_lit in H by lia; tac H; rewrite ?U_lit in H by lia;
try (apply (proj1 (negb_true_iff _)) in H); try (apply (proj1 (negb_false_iff _)) in H).
Ltac hc_prop H :=
first [ apply (proj1 (Z.eqb_eq _ _)) in H | apply (proj1 (Z.eqb_neq _ _)) in H
| apply (proj1 (Z.ltb_lt _ _)) in H | apply (proj1 (Z.ltb_ge _ _)) in H | idtac ].
Ltac rreg_byC HS r v pf H :=
lazymatch type of HS with st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (H : getr rg r = v) by (refine (eq_trans (st_ok_restrict_reg segs Hh Ex ss ms r HS) _); change (sv_denot Ex e = v); exact pf) end.
Section f.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis AMEMCMP : amemcmp_realizes trbsegs B A_memcmp_icpt.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let errno_low := tl_env B TL.
Definition tcmpF_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (g cfp bfp iCur iBef : Z) (gvals cvals bvals : list Z)
(gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z),
afn_pre trbsegs B TCMP_STK ly S W regs mem md ch ->
getr regs 10 = w64 g -> getr regs 11 = w64 cfp -> getr regs 12 = w64 bfp ->
getr regs 13 = w64 iCur -> getr regs 14 = w64 iBef -> 0 <= iCur < 256 -> 0 <= iBef < 256 ->
In (g, CGIF_SIZE) (ablocks B ly S) -> afobj B ly S W mem cfp 32 -> In (bfp, FRAME_SIZE) (ablocks B ly S) ->
obj_at trbsegs (mrestrict (w_H W) mem) g LAY_CGIF gvals -> nth_error gvals CG_pal = Some gpal -> nth_error gvals CG_ngp = Some ngp ->
obj_at trbsegs (mrestrict (w_H W) mem) cfp LAY_FrameConfig cvals -> nth_error cvals FR_lpal = Some cpal -> nth_error cvals FR_attr = Some cattr ->
nth_error cvals FR_nlp = Some cnlp -> nth_error cvals FR_ctidx = Some ctidx ->
obj_at trbsegs (mrestrict (w_H W) mem) bfp LAY_Frame bvals -> nth_error bvals FR_lpal = Some bpal -> nth_error bvals FR_attr = Some battr ->
nth_error bvals FR_nlp = Some bnlp -> nth_error bvals FR_ctidx = Some btidx ->
(Z.land cattr 1 <> 0 -> afobj B ly S W mem cpal (3 * cnlp)) ->
(Z.land battr 1 <> 0 -> exists Nl, In (bpal, Nl) (ablocks B ly S) /\ 3 * bnlp <= Nl) ->
(Z.land cattr 1 = 0 \/ Z.land battr 1 = 0 -> exists Np, In (gpal, Np) (ablocks B ly S) /\ 3 * ngp <= Np) ->
SRr trbsegs W (cfg_at trbsegs A_cmpPixel regs mem md)
(tcmp_post B regs ly S W mem md gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx iCur iBef).
Definition cmpF_regions : smem :=
[ stack_region 16; got_region; bcell_region 42;
YQ0b.mkRegion (Some 10%nat) 0 CGIF_SIZE 0 0 [YQ0b.mkChunk 24 (CVal 8 (SOff 32 0)); YQ0b.mkChunk 52 (CVal 2 (SOff 33 0))];
YQ0b.mkRegion (Some 11%nat) 0 32 0 0 [YQ0b.mkChunk 0 (CVal 8 (SOff 34 0)); YQ0b.mkChunk 16 (CVal 4 (SOff 35 0));
YQ0b.mkChunk 26 (CVal 2 (SOff 36 0)); YQ0b.mkChunk 28 (CVal 1 (SOff 37 0))];
YQ0b.mkRegion (Some 12%nat) 0 FRAME_SIZE 0 0 [YQ0b.mkChunk 0 (CVal 8 (SOff 38 0)); YQ0b.mkChunk 16 (CVal 4 (SOff 39 0));
YQ0b.mkChunk 26 (CVal 2 (SOff 40 0)); YQ0b.mkChunk 28 (CVal 1 (SOff 41 0))] ].
Definition cmpF_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 4096 140737479966720 4); (11%nat, mkAF 4096 140737479966720 3); (12%nat, mkAF 4096 140737479966720 4);
(13%nat, mkAF 0 255 0); (14%nat, mkAF 0 255 0);
(33%nat, mkAF 0 65535 0); (35%nat, mkAF 0 4294967295 0); (36%nat, mkAF 0 65535 0); (37%nat, mkAF 0 255 0);
(39%nat, mkAF 0 4294967295 0); (40%nat, mkAF 0 65535 0); (41%nat, mkAF 0 255 0);
(42%nat, mkAF SB SB 0) ] [] [].
Definition ss_cmpF : sstate := mkSS A_cmpPixel sr_atoms cmpF_regions None cmpF_facts.
Definition cmpF_SH : list shent := [ mkSHE 10 0 CGIF_SIZE; mkSHE 11 0 32; mkSHE 12 0 FRAME_SIZE ].
Lemma cmpF_entry : forall ly S W (regs : bvmap 5 word) mem md ch (g cfp bfp iCur iBef : Z) (gvals cvals bvals : list Z)
(gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z),
afn_pre trbsegs B TCMP_STK ly S W regs mem md ch ->
getr regs 10 = w64 g -> getr regs 11 = w64 cfp -> getr regs 12 = w64 bfp ->
getr regs 13 = w64 iCur -> getr regs 14 = w64 iBef -> 0 <= iCur < 256 -> 0 <= iBef < 256 ->
In (g, CGIF_SIZE) (ablocks B ly S) -> afobj B ly S W mem cfp 32 -> In (bfp, FRAME_SIZE) (ablocks B ly S) ->
obj_at trbsegs (mrestrict (w_H W) mem) g LAY_CGIF gvals -> nth_error gvals CG_pal = Some gpal -> nth_error gvals CG_ngp = Some ngp ->
obj_at trbsegs (mrestrict (w_H W) mem) cfp LAY_FrameConfig cvals -> nth_error cvals FR_lpal = Some cpal -> nth_error cvals FR_attr = Some cattr ->
nth_error cvals FR_nlp = Some cnlp -> nth_error cvals FR_ctidx = Some ctidx ->
obj_at trbsegs (mrestrict (w_H W) mem) bfp LAY_Frame bvals -> nth_error bvals FR_lpal = Some bpal -> nth_error bvals FR_attr = Some battr ->
nth_error bvals FR_nlp = Some bnlp -> nth_error bvals FR_ctidx = Some btidx ->
st_ok trbsegs (Ereg regs (cmp_extra gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx)) ss_cmpF
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_cmpPixel) mem (seg_rom trbsegs)))
/\ sh_ok trbsegs CBx cmpF_SH (Ereg regs (cmp_extra gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx)) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch g cfp bfp iCur iBef gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx
HPRE H10 H11 H12 H13 H14 RiC RiB Hg Hc Hb Og Ogpal Ongp Oc Ocpal Ocattr Ocnlp Octidx Ob Obpal Obattr Obnlp Obtidx.
pose proof (obj_at_nth trbsegs _ _ _ _ CG_pal _ _ Og eq_refl Ogpal) as [Mgpal Rgpal].
pose proof (obj_at_nth trbsegs _ _ _ _ CG_ngp _ _ Og eq_refl Ongp) as [Mngp Rngp].
pose proof (obj_at_nth trbsegs _ _ _ _ FR_lpal _ _ Oc eq_refl Ocpal) as [Mcpal Rcpal].
pose proof (obj_at_nth trbsegs _ _ _ _ FR_attr _ _ Oc eq_refl Ocattr) as [Mcattr Rcattr].
pose proof (obj_at_nth trbsegs _ _ _ _ FR_nlp _ _ Oc eq_refl Ocnlp) as [Mcnlp Rcnlp].
pose proof (obj_at_nth trbsegs _ _ _ _ FR_ctidx _ _ Oc eq_refl Octidx) as [Mctidx Rctidx].
pose proof (obj_at_nth trbsegs _ _ _ _ FR_lpal _ _ Ob eq_refl Obpal) as [Mbpal Rbpal].
pose proof (obj_at_nth trbsegs _ _ _ _ FR_attr _ _ Ob eq_refl Obattr) as [Mbattr Rbattr].
pose proof (obj_at_nth trbsegs _ _ _ _ FR_nlp _ _ Ob eq_refl Obnlp) as [Mbnlp Rbnlp].
pose proof (obj_at_nth trbsegs _ _ _ _ FR_ctidx _ _ Ob eq_refl Obtidx) as [Mbtidx Rbtidx].
cbn [fst snd N.to_nat Z.of_N] in Mgpal, Rgpal, Mngp, Rngp, Mcpal, Rcpal, Mcattr, Rcattr, Mcnlp, Rcnlp, Mctidx, Rctidx, Mbpal, Rbpal, Mbattr, Rbattr, Mbnlp, Rbnlp, Mbtidx, Rbtidx.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : TCMP_STK = 4112) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md g CGIF_SIZE HAR Hg) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g CGIF_SIZE HAR Hg) as Hgh_img.
destruct Hc as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA).
destruct (frames_bounds trbsegs _ LAWS _ _ _ _ _ _ _ HAR Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img.
assert (Hc4096 : 4096 <= cfp) by lia. assert (Hcceil : cfp + 32 <= alloc_ceiling) by lia. assert (Hch' : cfp + 32 <= 0x10000 \/ 0x600000 <= cfp) by (unfold off_img in Hfhigh_img; lia).
destruct (al_blocks _ _ LAWS ly S W mem md bfp FRAME_SIZE HAR Hb) as (Hb16 & Hb4096 & Hbceil & Hbh_ia & _ & _). pose proof (proj1 Hbh_ia) as Hbh.
pose proof (blk_off_img _ _ _ _ _ _ bfp FRAME_SIZE HAR Hb) as Hbh_img.
change (req_size CGIF_SIZE) with 96 in *. change (req_size FRAME_SIZE) with 40 in *.
change (2 ^ (8 * 8)) with (2 ^ 64) in *. change (2 ^ (8 * 4)) with 4294967296 in *. change (2 ^ (8 * 2)) with 65536 in *. change (2 ^ (8 * 1)) with 256 in *.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Ereg regs (cmp_extra gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 g) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 cfp) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 bfp) by (subst E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 iCur) by (subst E; rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (E14 : ew E 14 = Z_to_bv 64 iBef) by (subst E; rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact H14).
assert (E32 : ew E 32 = Z_to_bv 64 gpal) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 ngp) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 cpal) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 cattr) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 cnlp) by (subst E; exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 ctidx) by (subst E; exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 bpal) by (subst E; exact (ew_Ereg_extra regs _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 battr) by (subst E; exact (ew_Ereg_extra regs _ 7)).
assert (E40 : ew E 40 = Z_to_bv 64 bnlp) by (subst E; exact (ew_Ereg_extra regs _ 8)).
assert (E41 : ew E 41 = Z_to_bv 64 btidx) by (subst E; exact (ew_Ereg_extra regs _ 9)).
assert (E42 : ew E 42 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 10)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_cmpF. apply (entry_st_ok_full trbsegs); change (Ereg regs _) with E.
+ apply regs_ok_Ereg.
+ vm_compute. reflexivity.
+ unfold cmpF_regions, stack_region, got_region, bcell_region.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable trbsegs). apply Hpres. lia.
* cbn [base_val]. unfold A_GOT_shadow. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 668240) at 1.
apply (chunk_ok_val trbsegs E _ 0 668240 8 (SLit A_shadow_glob) A_shadow_glob); [reflexivity | unfold A_shadow_glob; zside | zside |].
exact (val_mem_of_rdword trbsegs (w_H W) mem _ _ Kgot).
* cbn [base_val]. unfold A_shadow_glob. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 701048) at 1.
apply (chunk_ok_val trbsegs E _ 0 701048 8 CBx SB);
[cbn [sv_denot CBx]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
exact (val_mem_of_rdword trbsegs (w_H W) mem _ _ Kcell).
* rewrite (VB 10%nat g E10) by lia. unfold CGIF_SIZE. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor]].
-- apply (chunk_ok_val trbsegs E _ g 24 8 _ gpal); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mgpal].
-- apply (chunk_ok_val trbsegs E _ g 52 2 _ ngp); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mngp].
* rewrite (VB 11%nat cfp E11) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
-- apply (chunk_ok_val trbsegs E _ cfp 0 8 _ cpal); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mcpal].
-- apply (chunk_ok_val trbsegs E _ cfp 16 4 _ cattr); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mcattr].
-- apply (chunk_ok_val trbsegs E _ cfp 26 2 _ cnlp); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mcnlp].
-- apply (chunk_ok_val trbsegs E _ cfp 28 1 _ ctidx); [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mctidx].
* rewrite (VB 12%nat bfp E12) by lia. unfold FRAME_SIZE. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
-- apply (chunk_ok_val trbsegs E _ bfp 0 8 _ bpal); [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mbpal].
-- apply (chunk_ok_val trbsegs E _ bfp 16 4 _ battr); [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mbattr].
-- apply (chunk_ok_val trbsegs E _ bfp 26 2 _ bnlp); [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mbnlp].
-- apply (chunk_ok_val trbsegs E _ bfp 28 1 _ btidx); [cbn [sv_denot]; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mbtidx].
+ apply pairwise_disjoint_of_extents. unfold cmpF_regions, stack_region, got_region, bcell_region, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi]. rewrite (VB 10%nat g E10), (VB 11%nat cfp E11), (VB 12%nat bfp E12) by lia.
cbn [base_val]. rewrite Usp. unfold A_GOT_shadow, A_shadow_glob, CGIF_SIZE, FRAME_SIZE.
pose proof (sep_block_frame trbsegs _ LAWS ly S _ _ _ g CGIF_SIZE cid pos HAR Hg Hfin) as D1.
pose proof (sep_blocks trbsegs _ LAWS ly S _ _ _ g CGIF_SIZE bfp FRAME_SIZE HAR Hg Hb ltac:(unfold CGIF_SIZE, FRAME_SIZE; intros X; injection X; lia)) as D2.
pose proof (sep_block_frame trbsegs _ LAWS ly S _ _ _ bfp FRAME_SIZE cid pos HAR Hb Hfin) as D3.
unfold zdisjoint, block_rng in D1, D2, D3. cbn [fst snd] in D1, D2, D3. change (req_size CGIF_SIZE) with 96 in D1, D2. change (req_size FRAME_SIZE) with 40 in D2, D3.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hgceil Hgh Hgh_img Hg4096 Hcceil Hch' Hc4096 Hbceil Hbh Hbh_img Hb4096 C1 C3 WS Hstk0 D1 D2 D3 Hflo Hfhi. clear. unfold off_img. intros.
repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [cmpF_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E11, E12, E13, E14, E33, E35, E36, E37, E39, E40, E41, E42, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
change (2 ^ 3) with 8.
revert Hslo Hshi H47 Hceil Hgceil Hgh Hgh_img Hg4096 Hg16 Hcceil Hch' Hc4096 Hcal Hbceil Hbh Hbh_img Hb4096 Hb16 Hal16 C1 C3 WS Hstk0
RiC RiB Rngp Rcattr Rcnlp Rctidx Rbattr Rbnlp Rbtidx. clear. unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, cmpF_SH. constructor; [|constructor; [|constructor; [|constructor]]].
+ apply (shent_ok_of_block trbsegs B LAWS ly S W mem md E CBx 10 g CGIF_SIZE 0 CGIF_SIZE HAR Hg).
* unfold U, CBx. cbn [sv_denot]. rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
* unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
* lia. * change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia.
+ apply (shent_ok_of_range trbsegs (w_H W) mem E CBx 11 cfp 32 cfp 0 32 HRA).
* unfold U, CBx. cbn [sv_denot]. rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
* unfold U. cbn [sv_denot]. rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
* lia. * lia. * shent_range_app.
+ apply (shent_ok_of_block trbsegs B LAWS ly S W mem md E CBx 12 bfp FRAME_SIZE 0 FRAME_SIZE HAR Hb).
* unfold U, CBx. cbn [sv_denot]. rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
* unfold U. cbn [sv_denot]. rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
* lia. * change (req_size FRAME_SIZE) with 40. unfold FRAME_SIZE. lia.
Qed.
Lemma cmp_tail : forall ly S W (regs : bvmap 5 word) mem md ch memT mdT (regsT : bvmap 5 word) (pb pc Nb Nc iCur iBef : Z),
afn_pre trbsegs B TCMP_STK ly S W regs mem md ch ->
ajournal trbsegs B TCMP_STK (spZ regs) [] ly S W mem md [] ly S W memT mdT 0 ->
getr regsT 10 = w64 (pb + 3 * iBef) -> getr regsT 11 = w64 (pc + 3 * iCur) -> getr regsT 12 = w64 3 ->
getr regsT 1 = getr regs 1 -> getr regsT 2 = getr regs 2 -> getr regsT 3 = getr regs 3 -> getr regsT 4 = getr regs 4 ->
aregs_preserved regs regsT ->
In (pb, Nb) (ablocks B ly S) -> 0 <= iBef -> 3 * iBef + 3 <= Nb ->
In (pc, Nc) (ablocks B ly S) -> 0 <= iCur -> 3 * iCur + 3 <= Nc ->
SRr trbsegs W (mkCfg (mkst regsT (Z_to_bv 64 A_memcmp_icpt) memT (seg_rom trbsegs)) mdT)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom trbsegs)) md2 /\
ajournal trbsegs B TCMP_STK (spZ regs) [] ly S W mem md [] ly S W mem2 md2 0 /\
aregs_preserved regs regs2 /\ getr regs2 10 = v /\
(v = w64 0 <-> forall i, 0 <= i < 3 -> aview trbsegs (w_H W) mem (pb + 3 * iBef + i) = aview trbsegs (w_H W) mem (pc + 3 * iCur + i))).
Proof.
intros ly S W regs mem md ch memT mdT regsT pb pc Nb Nc iCur iBef HPRE HJ Ha0 Ha1 Ha2 R1 R2 R3 R4 HPT HinB RiB HszB HinC RiC HszC.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (WS : TCMP_STK = 4112) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (proj1 HJ) as HART.
destruct (al_blocks _ _ LAWS ly S W memT mdT pb Nb HART HinB) as (_ & Hpb4096 & Hpbceil & Hpbh_ia & Hpbpres & _). pose proof (proj1 Hpbh_ia) as Hpbh.
pose proof (blk_off_img _ _ _ _ _ _ pb Nb HART HinB) as Hpbh_img.
destruct (al_blocks _ _ LAWS ly S W memT mdT pc Nc HART HinC) as (_ & Hpc4096 & Hpcceil & Hpch_ia & Hpcpres & _). pose proof (proj1 Hpch_ia) as Hpch.
pose proof (blk_off_img _ _ _ _ _ _ pc Nc HART HinC) as Hpch_img.
pose proof (req_size_pos Nb ltac:(lia)) as [_ HrNb]. pose proof (req_size_pos Nc ltac:(lia)) as [_ HrNc].
assert (Usp : spZ regsT = spZ regs + 0) by (unfold spZ; rewrite R2; lia).
eapply SRr_mono.
{ eapply (aj_memcmp_at trbsegs B LAWS Hsegs A_memcmp_icpt AMEMCMP W regsT memT TCMP_STK (spZ regs) [] ly S W mem md []
ly S mdT 0 (pb + 3 * iBef) (pc + 3 * iCur) 3 0 (getr regs 1) HJ Ha0 Ha1 Ha2).
- lia. - lia. - lia. - lia. - lia.
- exact Usp. - reflexivity. - lia. - rewrite WS. unfold ESTACK. lia.
- rewrite R3. exact Hgp. - rewrite R4. exact Htp. - exact R1. - exact Hra.
- intros a Ha. split; [apply (aview_some_of_apresent trbsegs); apply (fun Hq => proj1 (Hpbpres a Hq)); lia | rewrite Usp, Hes; lia].
- intros a Ha. split; [apply (aview_some_of_apresent trbsegs); apply (fun Hq => proj1 (Hpcpres a Hq)); lia | rewrite Usp, Hes; lia].
- apply (amem_range_of_block trbsegs B LAWS ly S _ _ _ pb Nb _ _ HART HinB); lia.
- apply (amem_range_of_block trbsegs B LAWS ly S _ _ _ pc Nc _ _ HART HinC); lia.
- apply (range_addressable_of_block trbsegs B LAWS ly S _ _ _ pb Nb _ _ HART HinB); lia.
- intros _. apply (shadow_hull_vis_of_block trbsegs B LAWS ly S _ _ _ pb Nb _ _ HART HinB); lia.
- apply (range_addressable_of_block trbsegs B LAWS ly S _ _ _ pc Nc _ _ HART HinC); lia.
- intros _. apply (shadow_hull_vis_of_block trbsegs B LAWS ly S _ _ _ pc Nc _ _ HART HinC); lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr & Hpr2).
split; [reflexivity|]. exists regs2, mem2, md2, v.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact (aregs_preserved_trans _ _ _ HPT HP2)|]. split; [exact Hv|].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
rewrite Hcmp. split; intros HQ i Hi.
- rewrite <- (Z.add_assoc pb), <- (Z.add_assoc pc). rewrite <- (F2 pb Nb (3 * iBef + i) HinB HinB ltac:(lia) ltac:(intros X; exact (inFP_nil _ X))).
rewrite <- (F2 pc Nc (3 * iCur + i) HinC HinC ltac:(lia) ltac:(intros X; exact (inFP_nil _ X))).
rewrite !Z.add_assoc. apply HQ. exact Hi.
- rewrite <- (Z.add_assoc pb), <- (Z.add_assoc pc). rewrite (F2 pb Nb (3 * iBef + i) HinB HinB ltac:(lia) ltac:(intros X; exact (inFP_nil _ X))).
rewrite (F2 pc Nc (3 * iCur + i) HinC HinC ltac:(lia) ltac:(intros X; exact (inFP_nil _ X))).
rewrite !Z.add_assoc. apply HQ. exact Hi.
Qed.
Lemma cmp_tailG : forall ly S W (regs : bvmap 5 word) mem md ch memT mdT (regsT : bvmap 5 word) (pb pc Nb nc iCur iBef : Z),
afn_pre trbsegs B TCMP_STK ly S W regs mem md ch ->
ajournal trbsegs B TCMP_STK (spZ regs) [] ly S W mem md [] ly S W memT mdT 0 ->
getr regsT 10 = w64 (pb + 3 * iBef) -> getr regsT 11 = w64 (pc + 3 * iCur) -> getr regsT 12 = w64 3 ->
getr regsT 1 = getr regs 1 -> getr regsT 2 = getr regs 2 -> getr regsT 3 = getr regs 3 -> getr regsT 4 = getr regs 4 ->
aregs_preserved regs regsT ->
In (pb, Nb) (ablocks B ly S) -> 0 <= iBef -> 3 * iBef + 3 <= Nb ->
afobj B ly S W mem pc nc -> 0 <= iCur -> 3 * iCur + 3 <= nc ->
SRr trbsegs W (mkCfg (mkst regsT (Z_to_bv 64 A_memcmp_icpt) memT (seg_rom trbsegs)) mdT)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom trbsegs)) md2 /\
ajournal trbsegs B TCMP_STK (spZ regs) [] ly S W mem md [] ly S W mem2 md2 0 /\
aregs_preserved regs regs2 /\ getr regs2 10 = v /\
(v = w64 0 <-> forall i, 0 <= i < 3 -> aview trbsegs (w_H W) mem (pb + 3 * iBef + i) = aview trbsegs (w_H W) mem (pc + 3 * iCur + i))).
Proof.
intros ly S W regs mem md ch memT mdT regsT pb pc Nb nc iCur iBef HPRE HJ Ha0 Ha1 Ha2 R1 R2 R3 R4 HPT HinB RiB HszB HFc RiC HszC.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (WS : TCMP_STK = 4112) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (proj1 HJ) as HART.
destruct (al_blocks _ _ LAWS ly S W memT mdT pb Nb HART HinB) as (_ & Hpb4096 & Hpbceil & Hpbh_ia & Hpbpres & _). pose proof (proj1 Hpbh_ia) as Hpbh.
pose proof (blk_off_img _ _ _ _ _ _ pb Nb HART HinB) as Hpbh_img.
destruct HFc as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hp8 & HRA).
destruct (frames_bounds trbsegs B LAWS ly S W memT mdT cid pos HART Hfin) as (Hf4096 & Hfceil & Hfhigh).
destruct (al_frames _ _ LAWS ly S W memT mdT cid pos HART Hfin) as (_ & _ & Hfpres & _).
pose proof (req_size_pos Nb ltac:(lia)) as [_ HrNb].
assert (Usp : spZ regsT = spZ regs + 0) by (unfold spZ; rewrite R2; lia).
eapply SRr_mono.
{ eapply (aj_memcmp_at trbsegs B LAWS Hsegs A_memcmp_icpt AMEMCMP W regsT memT TCMP_STK (spZ regs) [] ly S W mem md []
ly S mdT 0 (pb + 3 * iBef) (pc + 3 * iCur) 3 0 (getr regs 1) HJ Ha0 Ha1 Ha2).
- lia. - lia. - lia. - lia. - lia.
- exact Usp. - reflexivity. - lia. - rewrite WS. unfold ESTACK. lia.
- rewrite R3. exact Hgp. - rewrite R4. exact Htp. - exact R1. - exact Hra.
- intros a Ha. split; [apply (aview_some_of_apresent trbsegs); apply (fun Hq => proj1 (Hpbpres a Hq)); lia | rewrite Usp, Hes; lia].
- intros a Ha. split; [apply (aview_some_of_apresent trbsegs); apply (fun Hq => proj1 (Hfpres a Hq)); lia | rewrite Usp, Hes; lia].
- apply (amem_range_of_block trbsegs B LAWS ly S _ _ _ pb Nb _ _ HART HinB); lia.
- apply amem_range_high; [lia | destruct Hfhigh as [_ Hfz]; unfold kLowShadowBeg, kHighMemBeg in Hfz; lia | lia].
- apply (range_addressable_of_block trbsegs B LAWS ly S _ _ _ pb Nb _ _ HART HinB); lia.
- intros _. apply (shadow_hull_vis_of_block trbsegs B LAWS ly S _ _ _ pb Nb _ _ HART HinB); lia.
- eapply (range_addressable_entry_frame trbsegs B LAWS); [exact HJ | exact Hfin | exact Hcid0 | | | exact Hfal | intros x Hx; exfalso; exact (inFP_nil x Hx) | exact HAR | ];
[lia | lia | intros x Hx; apply HRA; lia].
- intros _. apply (shadow_hull_vis_of_frame trbsegs B LAWS ly S _ _ _ cid pos _ _ HART Hfin); lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr & Hpr2).
split; [reflexivity|]. exists regs2, mem2, md2, v.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact (aregs_preserved_trans _ _ _ HPT HP2)|]. split; [exact Hv|].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _ & F4 & _).
rewrite Hcmp. split; intros HQ i Hi.
- rewrite <- (Z.add_assoc pb), <- (Z.add_assoc pc). rewrite <- (F2 pb Nb (3 * iBef + i) HinB HinB ltac:(lia) ltac:(intros X; exact (inFP_nil _ X))).
rewrite <- (F4 cid pos (pc + (3 * iCur + i)) Hfin ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; lia) ltac:(intros X; exact (inFP_nil _ X))).
rewrite !Z.add_assoc. apply HQ. exact Hi.
- rewrite <- (Z.add_assoc pb), <- (Z.add_assoc pc). rewrite (F2 pb Nb (3 * iBef + i) HinB HinB ltac:(lia) ltac:(intros X; exact (inFP_nil _ X))).
rewrite (F4 cid pos (pc + (3 * iCur + i)) Hfin ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; lia) ltac:(intros X; exact (inFP_nil _ X))).
rewrite !Z.add_assoc. apply HQ. exact Hi.
Qed.
Theorem trb_cmpPixelF : tcmpF_spec.
Proof.
unfold tcmpF_spec.
intros ly S W regs mem md ch g cfp bfp iCur iBef gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx
HPRE H10 H11 H12 H13 H14 RiC RiB Hg Hc Hb Og Ogpal Ongp Oc Ocpal Ocattr Ocnlp Octidx Ob Obpal Obattr Obnlp Obtidx HLc HLb HGp.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
destruct (cmpF_entry ly S W regs mem md ch g cfp bfp iCur iBef gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx
HPRE H10 H11 H12 H13 H14 RiC RiB Hg Hc Hb Og Ogpal Ongp Oc Ocpal Ocattr Ocnlp Octidx Ob Obpal Obattr Obnlp Obtidx) as [HS SHOK].
pose proof (ajournal_init trbsegs B TCMP_STK [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (WS : TCMP_STK = 4112) by reflexivity.
pose proof (obj_at_nth trbsegs _ _ _ _ CG_pal _ _ Og eq_refl Ogpal) as [Mgpal Rgpal].
pose proof (obj_at_nth trbsegs _ _ _ _ CG_ngp _ _ Og eq_refl Ongp) as [Mngp Rngp].
pose proof (obj_at_nth trbsegs _ _ _ _ FR_lpal _ _ Oc eq_refl Ocpal) as [Mcpal Rcpal].
pose proof (obj_at_nth trbsegs _ _ _ _ FR_attr _ _ Oc eq_refl Ocattr) as [Mcattr Rcattr].
pose proof (obj_at_nth trbsegs _ _ _ _ FR_nlp _ _ Oc eq_refl Ocnlp) as [Mcnlp Rcnlp].
pose proof (obj_at_nth trbsegs _ _ _ _ FR_ctidx _ _ Oc eq_refl Octidx) as [Mctidx Rctidx].
pose proof (obj_at_nth trbsegs _ _ _ _ FR_lpal _ _ Ob eq_refl Obpal) as [Mbpal Rbpal].
pose proof (obj_at_nth trbsegs _ _ _ _ FR_attr _ _ Ob eq_refl Obattr) as [Mbattr Rbattr].
pose proof (obj_at_nth trbsegs _ _ _ _ FR_nlp _ _ Ob eq_refl Obnlp) as [Mbnlp Rbnlp].
pose proof (obj_at_nth trbsegs _ _ _ _ FR_ctidx _ _ Ob eq_refl Obtidx) as [Mbtidx Rbtidx].
cbn [fst snd N.to_nat Z.of_N] in Mgpal, Rgpal, Mngp, Rngp, Mcpal, Rcpal, Mcattr, Rcattr, Mcnlp, Rcnlp, Mctidx, Rctidx, Mbpal, Rbpal, Mbattr, Rbattr, Mbnlp, Rbnlp, Mbtidx, Rbtidx.
change (2 ^ (8 * 8)) with (2 ^ 64) in *. change (2 ^ (8 * 4)) with 4294967296 in *. change (2 ^ (8 * 2)) with 65536 in *. change (2 ^ (8 * 1)) with 256 in *.
destruct (al_blocks _ _ LAWS ly S W mem md g CGIF_SIZE HAR Hg) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & Hgpres & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g CGIF_SIZE HAR Hg) as Hgh_img.
destruct Hc as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA).
destruct (frames_bounds trbsegs _ LAWS _ _ _ _ _ _ _ HAR Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img.
assert (Hc4096 : 4096 <= cfp) by lia. assert (Hcceil : cfp + 32 <= alloc_ceiling) by lia. assert (Hch' : cfp + 32 <= 0x10000 \/ 0x600000 <= cfp) by (unfold off_img in Hfhigh_img; lia).
destruct (al_blocks _ _ LAWS ly S W mem md bfp FRAME_SIZE HAR Hb) as (Hb16 & Hb4096 & Hbceil & Hbh_ia & Hbpres & _). pose proof (proj1 Hbh_ia) as Hbh.
pose proof (blk_off_img _ _ _ _ _ _ bfp FRAME_SIZE HAR Hb) as Hbh_img.
change (req_size CGIF_SIZE) with 96 in *. change (req_size FRAME_SIZE) with 40 in *.
remember (Ereg regs (cmp_extra gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx)) as E eqn:HE.
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 g) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 cfp) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 bfp) by (subst E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 iCur) by (subst E; rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (E14 : ew E 14 = Z_to_bv 64 iBef) by (subst E; rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact H14).
assert (E32 : ew E 32 = Z_to_bv 64 gpal) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 ngp) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 cpal) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 cattr) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 cnlp) by (subst E; exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 ctidx) by (subst E; exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 bpal) by (subst E; exact (ew_Ereg_extra regs _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 battr) by (subst E; exact (ew_Ereg_extra regs _ 7)).
assert (E40 : ew E 40 = Z_to_bv 64 bnlp) by (subst E; exact (ew_Ereg_extra regs _ 8)).
assert (E41 : ew E 41 = Z_to_bv 64 btidx) by (subst E; exact (ew_Ereg_extra regs _ 9)).
assert (E42 : ew E 42 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 10)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (cmp_extra gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx)) E) by (rewrite HE; split; [intros n Hn; reflexivity | reflexivity]).
assert (HAE43 : env_agree 43 E E) by (split; [intros n Hn; reflexivity | reflexivity]).
clear HE.
unfold cfg_at. change (w64 A_cmpPixel) with (Z_to_bv 64 A_cmpPixel).
pose proof HJ as HJ0.
let normE H := repeat (match type of H with context [U ?Ex _] =>
lazymatch Ex with E => fail | _ =>
let HAGx := fresh "HAG" in
assert (HAGx : env_agree 43 E Ex) by (env_agree_chain HAE43);
rewrite !(U_agree 43 E _ _ HAGx) in H by (vm_compute; reflexivity); clear HAGx end end) in
let atoms H := normE H;
rewrite ?(U_atom E 13 iCur E13), ?(U_atom E 14 iBef E14), ?(U_atom E 33 ngp E33), ?(U_atom E 35 cattr E35),
?(U_atom E 36 cnlp E36), ?(U_atom E 37 ctidx E37), ?(U_atom E 39 battr E39), ?(U_atom E 40 bnlp E40),
?(U_atom E 41 btidx E41) in H by lia in
let leaf_ret := idtac;
lazymatch goal with HS : st_ok _ _ ?ssx (restrict _ ?msc), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
let R10 := fresh "R10" in let R1 := fresh "R1" in
rreg HS (10%bv : bv 5) R10; rreg HS (1%bv : bv 5) R1;
eapply (SRr_ret_at trbsegs trbtbl_lib trbtbl_lib_ok Hwx W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
let mat' := fresh "mat" in intros mat'; split; [reflexivity|];
eexists _, _, _, (getr (ms_regs msc) 10);
split; [cbn [ms_regs]; rewrite R1; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite E1, Hra; reflexivity|];
split; [cbn [ms_mem]; apply (ajournal_materialize trbsegs B LAWS Hsegs); exact HJ|];
split; [eapply (aregs_preserved_of_st_ok trbsegs _ _ _ _ regs (cmp_extra gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx) HS); [env_agree_chain HAE | vm_compute; reflexivity]|];
split; [reflexivity|];
cbn [ms_regs]; rewrite R10;
repeat match goal with H : branch_taken _ _ _ = _ |- _ => hc_bool H atoms end;
unfold tcmp_zero, tsel;
repeat match goal with H : (Z.land ?a 1 =? 0) = ?b |- context [Z.land ?a 1 =? 0] => rewrite H end;
repeat match goal with H : (_ =? _) = _ |- _ => hc_prop H | H : (_ <? _) = _ |- _ => hc_prop H end;
first [   split; [intros _ | intros _; reflexivity]; left; split; lia
|   split; [intros X; exfalso; exact (w64_1_ne_0 X) | intros [HZ | HZ]; exfalso; [lia | ]];
destruct HZ as (HZ1 & HZ2 & HZ3 & HZ4 & _);
repeat match goal with |- context [if ?c then _ else _] => destruct c eqn:? end;
repeat match goal with H : context [if ?c then _ else _] |- _ => destruct c eqn:? end;
repeat match goal with H : (_ =? _) = _ |- _ => hc_prop H end; lia
| match goal with |- ?g => idtac "LEAF-RET-FAIL" g end ] end in
let leaf_tail := idtac;
lazymatch goal with HS : st_ok _ _ ?ssx (restrict _ ?msc), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
repeat match goal with H : branch_taken _ _ _ = _ |- _ => hc_bool H atoms; let H' := fresh "P" in pose proof H as H'; hc_prop H' end;
let eb := eval vm_compute in (sr_get (ss_regs ssx) 10%bv) in
let ec := eval vm_compute in (sr_get (ss_regs ssx) 11%bv) in
lazymatch eb with SAlu ALU_ADD _ (SOff ?nb 0) =>
lazymatch ec with SAlu ALU_ADD _ (SOff ?nc 0) =>
let pb := lazymatch nb with 32%nat => gpal | _ => bpal end in
let pc := lazymatch nc with 32%nat => gpal | _ => cpal end in
let Enb := lazymatch nb with 32%nat => E32 | _ => E38 end in
let Enc := lazymatch nc with 32%nat => E32 | _ => E34 end in
let HinB := fresh "HinB" in let HszB := fresh "HszB" in let NB := fresh "NB" in
let HinC := fresh "HinC" in let HszC := fresh "HszC" in let NC := fresh "NC" in
first [ lazymatch nb with 32%nat => destruct (HGp ltac:(right; assumption)) as (NB & HinB & HszB)
| _ => destruct (HLb ltac:(assumption)) as (NB & HinB & HszB) end
| idtac "TAIL-NOBLOCK-B" nb; fail ];
first [ lazymatch nc with 32%nat => destruct (HGp ltac:(left; assumption)) as (NC & HinC & HszC)
| _ => pose proof (HLc ltac:(assumption)) as HinC end
| idtac "TAIL-NOBLOCK-C" nc; fail ];
let HB := fresh "HBb" in let HC := fresh "HBc" in let HBq := fresh "HBq" in let HCq := fresh "HCq" in
let RB := fresh "RBq" in let RC := fresh "RCq" in
destruct (al_blocks _ _ LAWS ly S W mem md pb NB HAR HinB) as (_ & HB & HBq & _);
pose proof (req_size_pos NB ltac:(clear - HszB RiB RiC Rngp Rcnlp Rbnlp; lia)) as [_ RB];
let SzB := fresh "SzB" in let SzC := fresh "SzC" in let BndB := fresh "BndB" in let BndC := fresh "BndC" in
assert (SzB : 3 * iBef + 3 <= NB) by lia;
assert (BndB : pb + 3 * iBef + 3 <= 2 ^ 63) by (clear - SzB HBq RB C1 RiB; lia);
lazymatch nc with
| 32%nat => destruct (al_blocks _ _ LAWS ly S W mem md pc NC HAR HinC) as (_ & HC & HCq & _);
pose proof (req_size_pos NC ltac:(clear - HszC RiB RiC Rngp Rcnlp Rbnlp; lia)) as [_ RC];
assert (SzC : 3 * iCur + 3 <= NC) by lia;
assert (BndC : pc + 3 * iCur + 3 <= 2 ^ 63) by (clear - SzC HCq RC C1 RiC; lia)
| _ =>
pose proof HinC as ((cidG & posG & HfinG & _ & _ & HfloG & HfhiG) & _ & _);
destruct (frames_bounds trbsegs _ LAWS _ _ _ _ _ _ _ HAR HfinG) as (HC0G & HCqG & _);
assert (HC : 4096 <= pc) by (clear - HC0G HfloG; lia);
assert (SzC : 3 * iCur + 3 <= 3 * cnlp) by lia;
assert (BndC : pc + 3 * iCur + 3 <= 2 ^ 63) by (clear - SzC HCqG HfhiG C1 RiC; lia)
end;
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Ra2 := fresh "Ra2" in
let Q1 := fresh "Q1" in let Q2 := fresh "Q2" in let Q3 := fresh "Q3" in let Q4 := fresh "Q4" in
rreg_byC HS (10%bv : bv 5) (Z_to_bv 64 (pb + 3 * iBef)) (denot_pal3 E nb 14 pb iBef Enb E14 ltac:(clear - HB; lia) BndB RiB) Ra0;
rreg_byC HS (11%bv : bv 5) (Z_to_bv 64 (pc + 3 * iCur)) (denot_pal3 E nc 13 pc iCur Enc E13 ltac:(clear - HC; lia) BndC RiC) Ra1;
rreg HS (12%bv : bv 5) Ra2;
rreg HS (1%bv : bv 5) Q1; rreg HS (2%bv : bv 5) Q2; rreg HS (3%bv : bv 5) Q3; rreg HS (4%bv : bv 5) Q4;
let HPT := fresh "HPT" in
pose proof (aregs_preserved_of_st_ok trbsegs _ _ _ _ regs (cmp_extra gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx) HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HPT;
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl); cbn [ss_pc]; change (Z_to_bv 64 271256) with (Z_to_bv 64 A_memcmp_icpt);
cbn [ms_regs ms_mem] in Ra0, Ra1, Ra2, Q1, Q2, Q3, Q4, HPT;
eapply SRr_mono;
[ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
lazymatch nc with
| 32%nat => eapply (cmp_tail ly S W regs mem md ch mT dT rT pb pc NB NC iCur iBef HPRE HJ)
| _ => eapply (cmp_tailG ly S W regs mem md ch mT dT rT pb pc NB (3 * cnlp) iCur iBef HPRE HJ) end end;
[ exact Ra0 | exact Ra1
| first [rewrite Ra2; reflexivity | match goal with |- ?g => idtac "SG3" g; fail end]
| first [rewrite Q1, E1; reflexivity | match goal with |- ?g => idtac "SG4" g; fail end]
| first [rewrite Q2, E2; reflexivity | match goal with |- ?g => idtac "SG5" g; fail end]
| first [rewrite Q3, E3; reflexivity | match goal with |- ?g => idtac "SG6" g; fail end]
| first [rewrite Q4, E4; reflexivity | match goal with |- ?g => idtac "SG7" g; fail end]
| first [exact HPT | match goal with |- ?g => idtac "SG8" g; fail end]
| exact HinB | clear - RiB; lia | exact SzB | exact HinC | clear - RiC; lia | exact SzC ]
| cbv beta;
let W2 := fresh "W2" in let c2 := fresh "c2" in let regs2 := fresh "regs2" in let mem2 := fresh "mem2" in let md2 := fresh "md2" in
let v := fresh "v" in let HJ2 := fresh "HJ2" in let HP2 := fresh "HP2" in let Hv := fresh "Hv" in let Hcmp := fresh "Hcmp" in
let HPP := fresh "HPP" in let HW2 := fresh "HW2" in let Hc2 := fresh "Hc2" in
intros W2 c2 Hwle2 HPP; destruct HPP as (HW2 & regs2 & mem2 & md2 & v & Hc2 & HJ2 & HP2 & Hv & Hcmp); subst W2 c2;
split; [reflexivity|]; exists regs2, mem2, md2, v;
split; [reflexivity|]; split; [exact HJ2|]; split; [exact HP2|]; split; [exact Hv|];
rewrite Hcmp; unfold tcmp_zero, tsel;
repeat match goal with H : (Z.land ?a 1 =? 0) = ?b |- context [Z.land ?a 1 =? 0] => rewrite H end;
split; [ intros HQ; right; split; [lia|]; split; [lia|]; split; [lia|]; split; [lia|]; exact HQ
| intros [HZ | (_ & _ & _ & _ & HQ)]; [exfalso; lia | exact HQ] ] ]
end end end in
let sel_one na k Mk HSname :=
lazymatch goal with
| Hb : branch_taken BC_NE (sv_denot ?Ex (SAlu ALU_AND (SOff na 0) (SLit 1))) (sv_denot _ (SLit 0)) = ?bb |- _ =>
lazymatch goal with HS : st_ok _ _ _ (restrict _ _) |- _ =>
let Hb2 := fresh "Hsel" in
pose proof Hb as Hb2; rewrite branch_ne_U in Hb2;
(lazymatch Ex with E => idtac | _ =>
let AG := fresh "HAGb" in assert (AG : env_agree 43 E Ex) by (env_agree_chain HAE43);
rewrite !(U_agree 43 E _ _ AG) in Hb2 by (vm_compute; reflexivity); clear AG end);
rewrite U_and_lit in Hb2 by lia;
first [rewrite (U_atom E 39 battr E39) in Hb2 by lia | rewrite (U_atom E 35 cattr E35) in Hb2 by lia];
rewrite U_lit in Hb2 by lia;
let nb := lazymatch bb with
| true => lazymatch na with 39%nat => constr:(38%nat) | 35%nat => constr:(34%nat) end
| false => constr:(32%nat) end in
let NB := fresh "Nsel" in let HinB := fresh "HinS" in let HszB := fresh "HszS" in
lazymatch bb with
| true => apply (proj1 (Bool.negb_true_iff _)) in Hb2; apply Z.eqb_neq in Hb2;
lazymatch na with
| 39%nat => destruct (HLb Hb2) as (NB & HinB & HszB)
| 35%nat => pose proof (HLc Hb2) as HinB end
| false => apply (proj1 (Bool.negb_false_iff _)) in Hb2; apply Z.eqb_eq in Hb2;
lazymatch na with
| 39%nat => destruct (HGp (or_intror Hb2)) as (NB & HinB & HszB)
| 35%nat => destruct (HGp (or_introl Hb2)) as (NB & HinB & HszB) end
end;
let HB := fresh "HloS" in let HBq := fresh "HhiS" in let RB := fresh "RqS" in let RBp := fresh "RpS" in
lazymatch type of HinB with
| afobj _ _ _ _ _ ?ppG ?nnG =>
(pose proof HinB as ((cidS & posS & HfinS & _ & _ & HfloS & HfhiS) & _ & _);
destruct (frames_bounds trbsegs _ LAWS _ _ _ _ _ _ _ HAR HfinS) as (HC0S & HCqS & _);
assert (HB : 4096 <= ppG) by (clear - HC0S HfloS; lia);
assert (HBq : ppG + nnG <= alloc_ceiling) by (clear - HCqS HfhiS; lia);
assert (RBp : 0 <= nnG) by (clear - Rcnlp; lia);
assert (RB : True) by exact I)
| _ => destruct (al_blocks _ _ LAWS ly S W mem md _ NB HAR HinB) as (_ & HB & HBq & _);
pose proof (req_size_pos NB ltac:(clear - HszB RiB RiC Rngp Rcnlp Rbnlp; lia)) as [RBp RB]
end;
let En := lazymatch nb with 32%nat => constr:(E32) | 34%nat => constr:(E34) | 38%nat => constr:(E38) end in
let Ek := lazymatch k with 14%nat => constr:(E14) | 13%nat => constr:(E13) end in
let Rk := lazymatch k with 14%nat => constr:(RiB) | 13%nat => constr:(RiC) end in
lazymatch type of HS with st_ok ?segs ?E0 ?ss ?ms =>
let Hf := fresh "Hf" in
assert (Hf : afact_ok E0 nb (mkAF 4096 140737479966720 0));
[ unfold afact_ok; cbn [af_lo af_hi af_al2];
(lazymatch E0 with E => idtac | _ =>
let AG := fresh "HAGs" in assert (AG : env_agree 43 E E0) by (env_agree_chain HAE43);
rewrite (proj1 AG nb) by (clear; lia); clear AG end);
rewrite En; rewrite unsigned_lit_small by lia;
rewrite Z.pow_0_r, Z.mod_1_r; repeat split; first [lia | reflexivity | match goal with |- ?g => idtac "FACTFAIL" g end]
| apply (st_ok_add_fact segs E0 ss ms nb _ HS) in Hf; clear HS;
let Hg := fresh "Hg" in
assert (Hg : branch_taken BC_GEU (sv_denot E0 (SAlu ALU_ADD (SMd M_MUL (SOff k 0) (SLit 3)) (SOff nb 0))) (sv_denot E0 (SOff nb 0)) = true);
[ rewrite branch_geu_U;
(lazymatch E0 with E => idtac | _ =>
let AG := fresh "HAGs" in assert (AG : env_agree 43 E E0) by (env_agree_chain HAE43);
rewrite !(U_agree 43 E _ _ AG) by (vm_compute; reflexivity); clear AG end);
rewrite (U_add_mul3 E k nb _ _ Ek Rk En) by (clear - HB HBq RB RBp C1 Rk; lia);
rewrite (U_atom E nb _ En) by (clear - HB HBq RB RBp C1; lia);
apply (proj2 (Bool.negb_true_iff _)); apply Z.ltb_ge; clear - Rk; lia
| lazymatch type of Hf with st_ok _ _ ?ss1 ?ms1 =>
apply (st_ok_add_cond segs E0 ss1 ms1 BC_GEU _ _ Hf) in Hg; clear Hf;
let Hg2 := fresh "Hg" in
assert (Hg2 : branch_taken BC_GEU (sv_denot E0 (SAlu ALU_ADD (SMd M_MUL (SOff k 0) (SLit 3)) (SOff nb 0))) (sv_denot E0 (SLit 1)) = true);
[ rewrite branch_geu_U;
(lazymatch E0 with E => idtac | _ =>
let AG := fresh "HAGs" in assert (AG : env_agree 43 E E0) by (env_agree_chain HAE43);
rewrite !(U_agree 43 E _ _ AG) by (vm_compute; reflexivity); clear AG end);
rewrite (U_add_mul3 E k nb _ _ Ek Rk En) by (clear - HB HBq RB RBp C1 Rk; lia);
rewrite U_lit by (clear; lia); apply (proj2 (Bool.negb_true_iff _)); apply Z.ltb_ge; clear - Rk HB; lia
| lazymatch type of Hg with st_ok _ _ ?ss2 ?ms2 =>
apply (st_ok_add_cond segs E0 ss2 ms2 BC_GEU _ _ Hg) in Hg2; clear Hg; rename Hg2 into HSname;
lazymatch type of HSname with st_ok _ _ ?ss3 _ => let ss4 := eval vm_compute in ss3 in change ss3 with ss4 in HSname end
end ]
end ]
];
assert (Mk) by exact I
end end
| |- _ => idtac
end in
let add_sel :=
(lazymatch goal with _ : selB_done |- _ => idtac | |- _ => sel_one 39%nat 14%nat selB_done HS end);
(lazymatch goal with _ : selC_done |- _ => idtac | |- _ => sel_one 35%nat 13%nat selC_done HS end) in
let rec go := idtac;
lazymatch goal with HS : st_ok _ _ ?ss0 _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok trbtbl_lib_ok HS HJ SHOK CBspan; [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |];
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
lazymatch goal with HS' : st_ok _ _ ?ss _, SHOK' : sh_ok _ _ _ _ _ |- _ =>
let pc := eval vm_compute in (ss_pc ss) in
lazymatch pc with
| 271256 => leaf_tail
| _ => let K := eval vm_compute in (run_K 0 CBx cmpF_SH ss) in
let why := sym_why_tok trbsegs trbtbl_lib K CBx CBspan cmpF_SH (start K CBx CBspan cmpF_SH ss) in
lazymatch why with
| SR_jalr _ => leaf_ret
| SR_branch _ _ _ => srr_branch_tok trbtbl_lib_ok HS' SHOK' CBspan; [add_sel; go | add_sel; go]
| _ => idtac "STUCK" pc why; fail
end
end end end in
go.
Qed.
End f.
End d.
