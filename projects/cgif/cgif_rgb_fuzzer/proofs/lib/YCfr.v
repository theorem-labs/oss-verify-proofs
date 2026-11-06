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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition A_freeCGIF : Z := 0x863a0.
Definition FC_STK : Z := 16 + ASTACK.
Definition CGIF_OBJ : Z := 96.
Definition fc_blocks (g pal attr ngp : Z) : list (Z * Z) :=
(g, CGIF_OBJ) :: (if Z.land attr 4 =? 0 then [(pal, 3 * ngp)] else []).
Section FC.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AFREE : afree_realizes trbsegs B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let errno_low := tl_env B TL.
Local Notation code := (as_code B).
Definition Bx : sv := SOff 34 0.
Definition fc_regions : smem :=
[ stack_region 16; got_region; bcell_region 34;
YQ0b.mkRegion (Some 10%nat) 0 CGIF_OBJ 0 0
[YQ0b.mkChunk 24 (CVal 8 (SOff 32 0)); YQ0b.mkChunk 40 (CVal 1 (SOff 33 0))] ].
Definition fc_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 4096 140737479966720 4); (33%nat, mkAF 0 255 0); (34%nat, mkAF SB SB 0) ] [] [].
Definition ss_fc : sstate := mkSS A_freeCGIF sr_atoms fc_regions None fc_facts.
Definition fc_SH : list shent := [ mkSHE 10 0 CGIF_OBJ ].
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition fc_extra (pal attr : Z) : list word := map (Z_to_bv 64) [pal; attr mod 256; SB].
Lemma fc_entry : forall W ly S regs mem md ch g pal attr ngp rest,
afn_pre trbsegs B FC_STK ly S W regs mem md ch ->
getr regs 10 = w64 g ->
val_mem trbsegs (mrestrict (w_H W) mem) (g + 24) 8 pal ->
val_mem trbsegs (mrestrict (w_H W) mem) (g + 40) 4 attr ->
0 <= pal < 2 ^ 64 -> 0 <= attr < 2 ^ 32 ->
Permutation (ablocks B ly S) (fc_blocks g pal attr ngp ++ rest) ->
st_ok trbsegs (Ereg regs (fc_extra pal attr)) ss_fc
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_freeCGIF) mem (seg_rom trbsegs)))
/\ sh_ok trbsegs Bx fc_SH (Ereg regs (fc_extra pal attr)) (mrestrict (w_H W) mem).
Proof.
intros W ly S regs mem md ch g pal attr ngp rest HPRE H10 Mpal Mattr Rpal Rattr HPerm.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : FC_STK = 16400) by reflexivity.
assert (Hing : In (g, CGIF_OBJ) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS ly S W mem md g CGIF_OBJ HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g CGIF_OBJ HAR Hing) as Hgh_img.
change (req_size CGIF_OBJ) with 96 in *.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Ereg regs (fc_extra pal attr)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 g) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 pal) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (attr mod 256)) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
pose proof (Z.mod_pos_bound attr 256 ltac:(lia)) as Hab.
split.
- unfold ss_fc. apply (entry_st_ok_full trbsegs); change (Ereg regs (fc_extra pal attr)) with E.
+ apply regs_ok_Ereg.
+ vm_compute. reflexivity.
+ unfold fc_regions, stack_region, got_region, bcell_region.
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
apply (chunk_ok_val trbsegs E _ 0 701048 8 Bx SB);
[cbn [sv_denot Bx]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
exact (val_mem_of_rdword trbsegs (w_H W) mem _ _ Kcell).
* rewrite (VB 10%nat g E10) by lia. unfold CGIF_OBJ. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor]].
-- apply (chunk_ok_val trbsegs E _ g 24 8 _ pal); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mpal].
-- apply (chunk_ok_val trbsegs E _ g 40 1 _ (attr mod 256)); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
exact (val_mem_byte0 trbsegs _ _ _ _ Mattr).
+ apply pairwise_disjoint_of_extents. unfold fc_regions, stack_region, got_region, bcell_region, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi]. rewrite (VB 10%nat g E10) by lia. cbn [base_val]. rewrite Usp.
unfold A_GOT_shadow, A_shadow_glob, CGIF_OBJ.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hgceil Hgh Hgh_img Hg4096 C1 C3 FFS Hstk0. clear. unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [fc_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E33, E34, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hgceil Hgh Hgh_img Hg4096 Hg16 Hal16 Hab C1 C3 FFS Hstk0. clear. unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, fc_SH. constructor; [|constructor].
apply (shent_ok_of_block trbsegs B LAWS ly S W mem md E Bx 10 g CGIF_OBJ 0 CGIF_OBJ HAR Hing).
+ unfold U, Bx. cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia.
+ change (req_size CGIF_OBJ) with 96. unfold CGIF_OBJ. lia.
Qed.
Definition fc_post (regs : bvmap 5 word) ly S W mem md (FP rest : list (Z * Z)) : world trbsegs -> config -> Prop :=
fun W' c' => exists ly' S' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom trbsegs)) md' /\
ajournal trbsegs B FC_STK (spZ regs) FP ly S W mem md [] ly' S' W' mem' md' 2 /\
aregs_preserved regs regs' /\ Permutation (ablocks B ly' S') rest.
Lemma fc_tail : forall W ly S regs mem md ch g pal attr ngp rest Wt regsT memT lyt St mdt kt,
afn_pre trbsegs B FC_STK ly S W regs mem md ch ->
In (call_trace0 (pc_free_ra0 Trb_code) regs ch) (as_universe B) ->
vev S + 2 <= VEV_MAX ->
ajournal trbsegs B FC_STK (spZ regs) (ablocks_fp (fc_blocks g pal attr ngp)) ly S W mem md [] lyt St Wt memT mdt kt ->
kt <= 1 ->
Permutation (ablocks B lyt St) ((g, CGIF_OBJ) :: rest) ->
aregs_preserved regs regsT -> getr regsT 10 = w64 g -> getr regsT 1 = getr regs 1 ->
SRr trbsegs Wt (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom trbsegs)) mdt)
(fc_post regs ly S W mem md (ablocks_fp (fc_blocks g pal attr ngp)) rest).
Proof.
intros W ly S regs mem md ch g pal attr ngp rest Wt regsT memT lyt St mdt kt
HPRE HU3 Hev HJ Hkt HPermR HP Ha0 Hra1.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (HARt & Hly & _ & _ & _ & _ & Hnev & _ & G1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (FFS : FC_STK = 16400) by reflexivity.
assert (HinfT : In (g, CGIF_OBJ) (ablocks B lyt St)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPermR|]. left. reflexivity. }
assert (P2 : getr regsT 2 = getr regs 2) by (apply (HP 2); left; reflexivity).
assert (P3 : getr regsT 3 = getr regs 3) by (apply (HP 3); right; left; reflexivity).
assert (P4 : getr regsT 4 = getr regs 4) by (apply (HP 4); right; right; left; reflexivity).
assert (P8 : getr regsT 8 = getr regs 8) by (apply (HP 8); right; right; right; left; reflexivity).
eapply SRr_mono.
{ eapply (aj_free_at trbsegs B LAWS trb_segs_low errno_low ML AFREE Wt regsT memT FC_STK (spZ regs) _ ly S W mem md [] lyt St mdt kt
g CGIF_OBJ 0 (getr regs 1) ch HJ HinfT Ha0).
- unfold spZ. rewrite P2. lia.
- reflexivity. - lia. - unfold FC_STK; lia.
- rewrite P3; exact Hgp. - rewrite P4; exact Htp.
- exact Hra1. - exact Hra. - lia.
- eapply (achain_chain_pre lyt _ (spZ regs) (s0Z regs) ch).
+ apply (achain_ly_top ly lyt). { destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & ET & _). exact ET. }
eapply (achain_kept ly _ _ (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia |].
intros a Ha. apply G1; lia.
+ change (spZ regsT) with (bv_unsigned (getr regsT 2)). rewrite P2. change (bv_unsigned (getr regs 2)) with (spZ regs). lia.
+ unfold s0Z. rewrite P8. reflexivity.
+ unfold raZ. rewrite Hra1. exact Hra4.
- unfold call_trace0, raZ in *. rewrite Hra1, HBcode. exact HU3.
- intros _ i Hi. apply (inFP_ablocks_fp _ g CGIF_OBJ i); [left; reflexivity | exact Hi]. }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (l1' & l2' & Ebl' & Ebl2') & _ & _).
exists ly3, S3, regs3, mem3, md3. split; [reflexivity|].
split; [eapply (ajournal_mono_k trbsegs B); [exact HJ3 | lia]|].
split; [eapply aregs_preserved_trans; [exact HP | exact HP3]|].
rewrite Ebl2'. apply Permutation_sym. apply (@Permutation_cons_app_inv _ _ l1' l2' (g, CGIF_OBJ)). rewrite <- Ebl'.
apply Permutation_sym. exact HPermR.
Qed.
Theorem trb_freeCGIF : forall W ly S regs mem md ch g pal attr ngp rest,
afn_pre trbsegs B FC_STK ly S W regs mem md ch ->
vev S + 2 <= VEV_MAX ->
getr regs 10 = w64 g ->
val_mem trbsegs (mrestrict (w_H W) mem) (g + 24) 8 pal ->
val_mem trbsegs (mrestrict (w_H W) mem) (g + 40) 4 attr ->
0 <= pal < 2 ^ 64 -> 0 <= attr < 2 ^ 32 -> 0 <= ngp ->
Permutation (ablocks B ly S) (fc_blocks g pal attr ngp ++ rest) ->
In [pc_free_ra0 Trb_code; 0x86400] (as_universe B) ->
In (call_trace0 (pc_free_ra0 Trb_code) regs ch) (as_universe B) ->
SRr trbsegs W (cfg_at trbsegs A_freeCGIF regs mem md)
(fc_post regs ly S W mem md (ablocks_fp (fc_blocks g pal attr ngp)) rest).
Proof.
intros W ly S regs mem md ch g pal attr ngp rest HPRE Hev H10 Mpal Mattr Rpal Rattr Rngp HPerm HU1 HU3.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
destruct (fc_entry W ly S regs mem md ch g pal attr ngp rest HPRE H10 Mpal Mattr Rpal Rattr HPerm) as [HS SHOK].
pose proof (ajournal_init trbsegs B FC_STK (ablocks_fp (fc_blocks g pal attr ngp)) ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (FFS : FC_STK = 16400) by reflexivity.
remember (Ereg regs (fc_extra pal attr)) as E eqn:HE.
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (subst E; exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 g) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 pal) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (attr mod 256)) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (fc_extra pal attr)) E) by (rewrite HE; split; [intros n Hn; reflexivity | reflexivity]).
clear HE.
assert (Hing : In (g, CGIF_OBJ) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS ly S W mem md g CGIF_OBJ HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g CGIF_OBJ HAR Hing) as Hgh_img.
change (req_size CGIF_OBJ) with 96 in Hgceil, Hgh, Hgh_img.
pose proof (Z.mod_pos_bound attr 256 ltac:(lia)) as Hab.
unfold cfg_at. change (w64 A_freeCGIF) with (Z_to_bv 64 A_freeCGIF).
aj_run_tok trbtbl_lib_ok HS HJ SHOK Bspan. { awr_ok_tac. exact Usp. }
srr_branch_tok trbtbl_lib_ok HS SHOK Bspan.
-
rewrite branch_ne_U, U_and_lit, (U_atom E 33 (attr mod 256) E33), U_lit, land_mod256_4 in Hc by lia.
assert (Hc' : (Z.land attr 4 =? 0) = false) by (destruct (Z.land attr 4 =? 0); [discriminate | reflexivity]).
unfold fc_blocks in HPerm. rewrite Hc' in HPerm. cbn [app] in HPerm.
aj_run_tok trbtbl_lib_ok HS HJ SHOK Bspan. { awr_ok_tac. exact Usp. }
rreg HS (10%bv : bv 5) R10. rreg HS (1%bv : bv 5) R1.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 340932 with (pc_wrap_free code) by (rewrite HBcode; reflexivity).
eapply (fc_tail W ly S regs mem md ch g pal attr ngp rest); [exact HPRE | exact HU3 | exact Hev | exact HJ | lia | exact HPerm | | |].
+ eapply (aregs_preserved_of_st_ok trbsegs _ E _ _ regs (fc_extra pal attr) HS); [exact HAE | vm_compute; reflexivity].
+ cbn [ms_regs]. rewrite R10, E10. reflexivity.
+ cbn [ms_regs]. rewrite R1, E1. reflexivity.
-
rewrite branch_ne_U, U_and_lit, (U_atom E 33 (attr mod 256) E33), U_lit, land_mod256_4 in Hc by lia.
assert (Hc' : (Z.land attr 4 =? 0) = true) by (destruct (Z.land attr 4 =? 0); [reflexivity | discriminate]).
pose proof HPerm as HPerm0. unfold fc_blocks in HPerm. rewrite Hc' in HPerm. cbn [app] in HPerm.
aj_run_tok trbtbl_lib_ok HS HJ SHOK Bspan. { awr_ok_tac. exact Usp. }
assert (Hinp : In (pal, 3 * ngp) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. right. left. reflexivity. }
pose proof (sep_blocks_perm trbsegs B LAWS ly S W mem md _ _ _ HAR HPerm) as Hd1. unfold zdisjoint, block_rng in Hd1. cbn [fst snd] in Hd1.
change (req_size CGIF_OBJ) with 96 in Hd1.
pose proof (proj1 HJ) as HARc.
lazymatch goal with |- SRr _ _ (mkCfg ?ms ?mdc) _ =>
rreg HS (2%bv : bv 5) R2; rreg HS (10%bv : bv 5) R10; rreg HS (3%bv : bv 5) R3; rreg HS (4%bv : bv 5) R4;
rreg HS (1%bv : bv 5) R1; rreg HS (8%bv : bv 5) R8;
eapply SRr_bind;
[ eapply (aj_free trbsegs B LAWS Hsegs errno_low ML AFREE W E _ ms FC_STK (spZ regs) _ ly S W mem md [] ly S _ 0
pal (3 * ngp) (-16) (ew E 2) (Z_to_bv 64 0x86400) []);
[ exact HS | rewrite HBcode; reflexivity | reflexivity | exact HJ | exact Hinp
| rewrite R10, E32; reflexivity
| exact (st_ok_restrict_reg trbsegs (w_H W) E _ _ 2%bv HS)
| reflexivity | exact Usp | reflexivity | lia | unfold FC_STK; lia
| rewrite R3, E3; exact Hgp | rewrite R4, E4; exact Htp
| exact R1 | vm_compute; reflexivity | lia
| eapply (achain_chain_pre ly _ (spZ regs - 16) g []);
[ apply achain_low; lia
| change (spZ (ms_regs ms)) with (bv_unsigned (getr (ms_regs ms) 2)); rewrite R2, unsigned_lit_small by lia; lia
| unfold s0Z; rewrite R8, E10; apply unsigned_lit_small; lia
| unfold raZ; rewrite R1; rewrite unsigned_lit_small by lia; lia ]
| rewrite call_trace_nil; unfold raZ; rewrite R1, unsigned_lit_small by lia; rewrite HBcode; cbn; exact HU1
| intros _ i Hi; apply (inFP_ablocks_fp _ pal (3 * ngp) i); [| exact Hi];
unfold fc_blocks; rewrite Hc'; right; left; reflexivity ]
| ]
end.
clear HJ SHOK R2 R10 R3 R4 R1 R8.
intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HP2 & (l1 & l2 & Ebl & Ebl2) & Hfrs2 & HK).
pose proof (proj1 HJ) as HAR2.
destruct (al_const _ _ LAWS _ _ _ _ _ HARc) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR2) as (Kcell2 & _ & Kgot2 & _). rewrite HBgot, HBcell in Kgot2. rewrite HBcell in Kcell2.
assert (HPerm2 : Permutation (ablocks B ly2 S2) ((g, CGIF_OBJ) :: rest)).
{ rewrite Ebl2. apply Permutation_sym. apply (@Permutation_cons_app_inv _ _ l1 l2 (pal, 3 * ngp)). rewrite <- Ebl.
apply Permutation_sym. eapply Permutation_trans; [exact HPerm|]. apply perm_swap. }
assert (Hing2 : In (g, CGIF_OBJ) (ablocks B ly2 S2)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm2|]. left. reflexivity. }
jafter_call HS 35%nat regs2 (mrestrict (w_H W2) mem2) HP2 HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | apply Forall_nil].
- eapply (region_kept_stack_aj trbsegs B); [exact HK | exact HJ | exact Usp | lia | unfold FC_STK, ASTACK; lia | lia | lia | lia].
- apply (region_kept_val trbsegs E _ _ A_GOT_shadow 8 A_shadow_glob);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot2) | lia].
- apply (region_kept_val trbsegs E _ _ A_shadow_glob 8 SHADOW_OFF);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell2) | lia].
- eapply (region_kept_block_aj trbsegs B); [exact HK | rewrite E10; apply unsigned_lit_small; lia | exact Hing | lia
| change (req_size CGIF_OBJ) with 96; unfold CGIF_OBJ; lia | lia | unfold CGIF_OBJ; intros a Ha HE'; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 35 (map (getr regs2) CLOB)) as E2' eqn:HE2' in HS.
assert (OLD2 : forall n, (n < 35)%nat -> ew E2' n = ew E n) by (intros n Hn; rewrite HE2'; apply YO3v.ew_havoc_old; exact Hn).
assert (HAE2 : env_agree 32 (Ereg regs (fc_extra pal attr)) E2') by (rewrite HE2'; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HE2'.
assert (F10 : ew E2' 10 = Z_to_bv 64 g) by (rewrite OLD2 by (cbv; lia); exact E10).
assert (F34 : ew E2' 34 = Z_to_bv 64 SB) by (rewrite OLD2 by (cbv; lia); exact E34).
assert (F1 : ew E2' 1 = getr regs 1) by (rewrite OLD2 by (cbv; lia); exact E1).
assert (Usp2 : bv_unsigned (ew E2' 2) = spZ regs) by (rewrite OLD2 by (cbv; lia); exact Usp).
assert (SHOK : sh_ok trbsegs Bx fc_SH E2' (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, fc_SH. constructor; [|constructor].
apply (shent_ok_of_block trbsegs B LAWS ly2 S2 W2 mem2 md2 E2' Bx 10 g CGIF_OBJ 0 CGIF_OBJ HAR2 Hing2).
+ unfold U, Bx. cbn [sv_denot]. rewrite F34, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite F10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia.
+ change (req_size CGIF_OBJ) with 96. unfold CGIF_OBJ. lia. }
aj_run_tok trbtbl_lib_ok HS HJ SHOK Bspan. { awr_ok_tac. exact Usp2. }
rreg HS (10%bv : bv 5) R10. rreg HS (1%bv : bv 5) R1.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 340932 with (pc_wrap_free code) by (rewrite HBcode; reflexivity).
eapply (fc_tail W ly S regs mem md ch g pal attr ngp rest); [exact HPRE | exact HU3 | exact Hev | exact HJ | lia | exact HPerm2 | | |].
+ eapply (aregs_preserved_of_st_ok trbsegs _ E2' _ _ regs (fc_extra pal attr) HS); [exact HAE2 | vm_compute; reflexivity].
+ cbn [ms_regs]. rewrite R10, F10. reflexivity.
+ cbn [ms_regs]. rewrite R1, F1. reflexivity.
Qed.
End FC.
End b.
