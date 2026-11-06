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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCe9 YCi1 YCib.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AFREE : afree_realizes trbsegs B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let errno_low := tl_env B TL.
Local Abbreviation code := (as_code B).
Definition Bx : sv := SOff 35 0.
Definition fc_regions : smem :=
[ stack_region 32; got_region; bcell_region 35;
YQ0b.mkRegion (Some 10%nat) 0 CHT_SIZE 0 0
[YQ0b.mkChunk 0 (CVal 8 (SOff 32 0)); YQ0b.mkChunk 8 (CVal 8 (SOff 33 0)); YQ0b.mkChunk 16 (CVal 8 (SOff 34 0));
YQ0b.mkChunk 24 (CVal 8 (SOff 36 0)); YQ0b.mkChunk 32 (CVal 8 (SOff 37 0))] ].
Definition fc_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 4096 140737479966720 4);
(32%nat, mkAF 0 (2^64 - 1) 0); (33%nat, mkAF 0 (2^64 - 1) 0); (34%nat, mkAF 0 (2^64 - 1) 0);
(35%nat, mkAF SB SB 0); (36%nat, mkAF 0 (2^64 - 1) 0); (37%nat, mkAF 0 (2^64 - 1) 0) ] [] [].
Definition ss_fc : sstate := mkSS A_free_col_hash_table sr_atoms fc_regions None fc_facts.
Definition fc_SH : list shent := [ mkSHE 10 0 CHT_SIZE ].
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition fc_extra (f h u p x : Z) : list word := map (Z_to_bv 64) [f; h; u; SB; p; x].
Lemma fc_entry : forall W ly S regs mem md ch c f h u p x rest,
afn_pre trbsegs B TFREECHT_STK ly S W regs mem md ch ->
getr regs 10 = w64 c ->
Permutation (ablocks B ly S) ((c, CHT_SIZE) :: rest) ->
val_mem trbsegs (mrestrict (w_H W) mem) c 8 f -> val_mem trbsegs (mrestrict (w_H W) mem) (c + 8) 8 h ->
val_mem trbsegs (mrestrict (w_H W) mem) (c + 16) 8 u -> val_mem trbsegs (mrestrict (w_H W) mem) (c + 24) 8 p ->
val_mem trbsegs (mrestrict (w_H W) mem) (c + 32) 8 x ->
0 <= f < 2 ^ 64 -> 0 <= h < 2 ^ 64 -> 0 <= u < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> 0 <= x < 2 ^ 64 ->
st_ok trbsegs (Ereg regs (fc_extra f h u p x)) ss_fc
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_free_col_hash_table) mem (seg_rom trbsegs)))
/\ sh_ok trbsegs Bx fc_SH (Ereg regs (fc_extra f h u p x)) (mrestrict (w_H W) mem).
Proof.
intros W ly S regs mem md ch c f h u p x rest HPRE H10 HPerm Mf Mh Mu Mp Mx Rf Rh Ru Rp Rx.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : TFREECHT_STK = 16416) by reflexivity.
assert (Hinc : In (c, CHT_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS ly S W mem md c CHT_SIZE HAR Hinc) as (Hc16 & Hc4096 & Hcceil & Hch_ia & _ & _). pose proof (proj1 Hch_ia) as Hchh.
pose proof (blk_off_img _ _ _ _ _ _ c CHT_SIZE HAR Hinc) as Hch_img.
change (req_size CHT_SIZE) with 48 in *.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Ereg regs (fc_extra f h u p x)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 c) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (EX : forall j, ew E (32 + j) = nth j (fc_extra f h u p x) (Z_to_bv 64 0)) by (intros j; subst E; apply ew_Ereg_extra).
pose proof (EX 0%nat) as E32. pose proof (EX 1%nat) as E33. pose proof (EX 2%nat) as E34. pose proof (EX 3%nat) as E35.
pose proof (EX 4%nat) as E36. pose proof (EX 5%nat) as E37.
cbn [Nat.add nth fc_extra map] in E32, E33, E34, E35, E36, E37. clear EX.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_fc. apply (entry_st_ok_full trbsegs); change (Ereg regs (fc_extra f h u p x)) with E.
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
[cbn [sv_denot Bx]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
exact (val_mem_of_rdword trbsegs (w_H W) mem _ _ Kcell).
* rewrite (VB 10%nat c E10) by lia. unfold CHT_SIZE. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat (constructor; [|]); [ | | | | | constructor].
-- apply (chunk_ok_val trbsegs E _ c 0 8 _ f); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Mf].
-- apply (chunk_ok_val trbsegs E _ c 8 8 _ h); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mh].
-- apply (chunk_ok_val trbsegs E _ c 16 8 _ u); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mu].
-- apply (chunk_ok_val trbsegs E _ c 24 8 _ p); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mp].
-- apply (chunk_ok_val trbsegs E _ c 32 8 _ x); [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mx].
+ apply pairwise_disjoint_of_extents. unfold fc_regions, stack_region, got_region, bcell_region, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi]. rewrite (VB 10%nat c E10) by lia. cbn [base_val]. rewrite Usp.
unfold A_GOT_shadow, A_shadow_glob, CHT_SIZE.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hcceil Hchh Hch_img Hc4096 C1 C3 FFS Hstk0. clear. unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [fc_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, E33, E34, E35, E36, E37, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hcceil Hchh Hch_img Hc4096 Hc16 Hal16 Rf Rh Ru Rp Rx C1 C3 FFS Hstk0. clear. unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, fc_SH. constructor; [|constructor].
apply (shent_ok_of_block trbsegs B LAWS ly S W mem md E Bx 10 c CHT_SIZE 0 CHT_SIZE HAR Hinc).
* unfold U, Bx. cbn [sv_denot]. rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
* unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
* lia.
* change (req_size CHT_SIZE) with 48. unfold CHT_SIZE. lia.
Qed.
Definition fc_post (regs : bvmap 5 word) ly S W mem md (FP rest : list (Z * Z)) : world trbsegs -> config -> Prop :=
fun W' c' => exists ly' S' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom trbsegs)) md' /\
ajournal trbsegs B TFREECHT_STK (spZ regs) FP ly S W mem md [] ly' S' W' mem' md' EV_FREECHT /\
aregs_preserved regs regs' /\ Permutation (ablocks B ly' S') rest.
Lemma fc_tail : forall W ly S regs mem md ch c FP rest Wt regsT memT lyt St mdt kt,
afn_pre trbsegs B TFREECHT_STK ly S W regs mem md ch ->
In (call_trace0 (pc_free_ra0 Trb_code) regs ch) (as_universe B) ->
vev S + EV_FREECHT <= VEV_MAX ->
ajournal trbsegs B TFREECHT_STK (spZ regs) FP ly S W mem md [] lyt St Wt memT mdt kt ->
kt <= 5 ->
Permutation (ablocks B lyt St) ((c, CHT_SIZE) :: rest) ->
(forall i, 0 <= i < req_size CHT_SIZE -> inFP FP (c + i)) ->
aregs_preserved regs regsT -> getr regsT 10 = w64 c -> getr regsT 1 = getr regs 1 ->
SRr trbsegs Wt (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom trbsegs)) mdt)
(fc_post regs ly S W mem md FP rest).
Proof.
intros W ly S regs mem md ch c FP rest Wt regsT memT lyt St mdt kt HPRE HU Hev HJ Hkt HPermR HFPc HP Ha0 Hra1.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (HARt & Hly & _ & _ & _ & _ & Hnev & _ & G1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (FFS : TFREECHT_STK = 16416) by reflexivity.
assert (HEVC : EV_FREECHT = 6) by reflexivity.
assert (HincT : In (c, CHT_SIZE) (ablocks B lyt St)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPermR|]. left. reflexivity. }
assert (P2 : getr regsT 2 = getr regs 2) by (apply (HP 2); left; reflexivity).
assert (P3 : getr regsT 3 = getr regs 3) by (apply (HP 3); right; left; reflexivity).
assert (P4 : getr regsT 4 = getr regs 4) by (apply (HP 4); right; right; left; reflexivity).
assert (P8 : getr regsT 8 = getr regs 8) by (apply (HP 8); right; right; right; left; reflexivity).
eapply SRr_mono.
{ eapply (aj_free_at trbsegs B LAWS trb_segs_low errno_low ML AFREE Wt regsT memT TFREECHT_STK (spZ regs) _ ly S W mem md [] lyt St mdt kt
c CHT_SIZE 0 (getr regs 1) ch HJ HincT Ha0).
- unfold spZ. rewrite P2. lia.
- reflexivity. - lia. - rewrite FFS. replace ASTACK with 16384 by reflexivity. lia.
- rewrite P3; exact Hgp. - rewrite P4; exact Htp.
- exact Hra1. - exact Hra. - rewrite HEVC in Hev. lia.
- eapply (achain_chain_pre lyt _ (spZ regs) (s0Z regs) ch).
+ apply (achain_ly_top ly lyt). { destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & ET & _). exact ET. }
eapply (achain_kept ly _ _ (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia |].
intros a Ha. apply G1; lia.
+ change (spZ regsT) with (bv_unsigned (getr regsT 2)). rewrite P2. change (bv_unsigned (getr regs 2)) with (spZ regs). lia.
+ unfold s0Z. rewrite P8. reflexivity.
+ unfold raZ. rewrite Hra1. exact Hra4.
- unfold call_trace0, raZ in *. rewrite Hra1, HBcode. exact HU.
- intros _ i Hi. exact (HFPc i Hi). }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (l1' & l2' & Ebl' & Ebl2') & _ & _).
exists ly3, S3, regs3, mem3, md3. split; [reflexivity|].
split; [eapply (ajournal_mono_k trbsegs B); [exact HJ3 | rewrite HEVC; lia]|].
split; [eapply aregs_preserved_trans; [exact HP | exact HP3]|].
rewrite Ebl2'. apply Permutation_sym. apply (@Permutation_cons_app_inv _ _ l1' l2' (c, CHT_SIZE)). rewrite <- Ebl'.
apply Permutation_sym. exact HPermR.
Qed.
Theorem trb_free_col_hash_table : tfree_cht_spec B.
Proof.
unfold tfree_cht_spec.
intros ly0 S0 W0 regs mem0 md0 ch c f h u p x nf nh nu np nx rest HPRE HCTX H10 Mf Mh Mu Mp Mx Rf Rh Ru Rp Rx HPerm0 Hev.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (FFS : TFREECHT_STK = 16416) by reflexivity.
assert (HEVC : EV_FREECHT = 6) by reflexivity.
assert (Hinc0 : In (c, CHT_SIZE) (ablocks B ly0 S0)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm0|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS ly0 S0 W0 mem0 md0 c CHT_SIZE HAR Hinc0) as (Hc16 & Hc4096 & Hcceil & _).
change (req_size CHT_SIZE) with 48 in Hcceil.
destruct (fc_entry W0 ly0 S0 regs mem0 md0 ch c f h u p x _ HPRE H10 HPerm0 Mf Mh Mu Mp Mx Rf Rh Ru Rp Rx) as [HS SHOK].
set (FPc := ablocks_fp ((c, CHT_SIZE) :: optb f nf ++ optb h nh ++ optb u nu ++ optb p np ++ optb x nx)).
assert (HU0 : In (call_trace0 (pc_free_ra0 Trb_code) regs ch) (as_universe B)).
{ rewrite (tl_universe B TL). exact (rg_trace0_of_ctx CTX_free_col_hash_table Trb_universe (pc_free_ra0 Trb_code) regs ch ltac:(vm_compute; reflexivity) HCTX). }
pose proof (ajournal_init trbsegs B TFREECHT_STK FPc ly0 S0 W0 regs mem0 md0 ch HPRE) as HJ.
remember (Ereg regs (fc_extra f h u p x)) as E0 eqn:HE.
assert (A1_0 : ew E0 1 = getr regs 1) by (subst E0; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (A2_0 : ew E0 2 = getr regs 2) by (subst E0; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (A3_0 : ew E0 3 = getr regs 3) by (subst E0; exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (A4_0 : ew E0 4 = getr regs 4) by (subst E0; exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (A10_0 : ew E0 10 = Z_to_bv 64 c) by (subst E0; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (A32_0 : ew E0 32 = Z_to_bv 64 f) by (subst E0; exact (ew_Ereg_extra regs _ 0)).
assert (A33_0 : ew E0 33 = Z_to_bv 64 h) by (subst E0; exact (ew_Ereg_extra regs _ 1)).
assert (A34_0 : ew E0 34 = Z_to_bv 64 u) by (subst E0; exact (ew_Ereg_extra regs _ 2)).
assert (A35_0 : ew E0 35 = Z_to_bv 64 SB) by (subst E0; exact (ew_Ereg_extra regs _ 3)).
assert (A36_0 : ew E0 36 = Z_to_bv 64 p) by (subst E0; exact (ew_Ereg_extra regs _ 4)).
assert (A37_0 : ew E0 37 = Z_to_bv 64 x) by (subst E0; exact (ew_Ereg_extra regs _ 5)).
assert (Usp_0 : bv_unsigned (ew E0 2) = spZ regs) by (rewrite A2_0; reflexivity).
assert (HAE_0 : env_agree 32 (Ereg regs (fc_extra f h u p x)) E0) by (rewrite HE; split; [intros n Hn; reflexivity | reflexivity]).
clear HE.
unfold cfg_at. change (w64 A_free_col_hash_table) with (Z_to_bv 64 A_free_col_hash_table).
aj_run_tok trbtbl_lib_ok HS HJ SHOK Bspan. { awr_ok_tac; exact Usp_0. }
assert (HU1 : In [pc_free_ra0 Trb_code; 0x84f50] (as_universe B)) by (rewrite (tl_universe B TL); apply memZL_In; vm_compute; reflexivity).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev0 & _).
pose proof (proj1 HJ) as HARc0.
lazymatch goal with |- SRr _ _ (mkCfg ?ms ?mdc) _ =>
rreg HS (2%bv : bv 5) R2; rreg HS (10%bv : bv 5) R10; rreg HS (3%bv : bv 5) R3; rreg HS (4%bv : bv 5) R4;
rreg HS (1%bv : bv 5) R1; rreg HS (8%bv : bv 5) R8;
eapply SRr_bind;
[ eapply (rg_aj_free_opt B LAWS Hsegs errno_low ML AFREE W0 E0 _ ms TFREECHT_STK (spZ regs) _ ly0 S0 W0 mem0 md0 [] ly0 S0 _ _
f nf (-32) (ew E0 2) (Z_to_bv 64 0x84f50) [] ((c, CHT_SIZE) :: optb h nh ++ optb u nu ++ optb p np ++ optb x nx ++ rest));
[ exact HS | rewrite HBcode; reflexivity | reflexivity | exact HJ
| eapply Permutation_trans; [exact HPerm0 | apply Permutation_middle]
| rewrite R10, A32_0; reflexivity
| exact (st_ok_restrict_reg trbsegs (w_H W0) E0 _ _ 2%bv HS)
| reflexivity | exact Usp_0 | reflexivity | lia | rewrite FFS; replace ASTACK with 16384 by reflexivity; lia
| rewrite R3, A3_0; exact Hgp | rewrite R4, A4_0; exact Htp
| exact R1 | vm_compute; reflexivity | rewrite HEVC in Hev; clear - Hev Hnev0; lia
| eapply (achain_chain_pre ly0 _ (spZ regs - 32) c []);
[ apply achain_low; clear - Hcceil; lia
| change (spZ (ms_regs ms)) with (bv_unsigned (getr (ms_regs ms) 2)); rewrite R2, unsigned_lit_small by lia; lia
| unfold s0Z; rewrite R8, A10_0; apply unsigned_lit_small; clear - Hc4096 Hcceil C1; lia
| unfold raZ; rewrite R1; rewrite unsigned_lit_small by lia; lia ]
| rewrite call_trace_nil; unfold raZ; rewrite R1, unsigned_lit_small by lia; rewrite HBcode; cbn; exact HU1
| intros Hb0 _ i Hi; apply (inFP_ablocks_fp _ f nf i); [right; apply in_app_iff; left; exact (rg_optb_in _ _ Hb0) | exact Hi] ]
| ]
end.
clear HJ SHOK R2 R10 R3 R4 R1 R8.
cbv beta. intros W1 c1 Hwle1 (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ & HP1 & HPerm1 & Hfrs1 & HK1).
pose proof (proj1 HJ) as HAR1.
destruct (al_const _ _ LAWS _ _ _ _ _ HARc0) as (Kcell1a & _ & Kgot1a & _). rewrite HBgot, HBcell in Kgot1a. rewrite HBcell in Kcell1a.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR1) as (Kcell1 & _ & Kgot1 & _). rewrite HBgot, HBcell in Kgot1. rewrite HBcell in Kcell1.
assert (Hinc1 : In (c, CHT_SIZE) (ablocks B ly1 S1)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. left. reflexivity. }
jafter_call_keep HS 40%nat regs1 (mrestrict (w_H W1) mem1) HP1 [0; 1; 2; 3]%nat HSn.
match type of HSn with ?t -> _ => assert (HRK : t); [|specialize (HSn HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | apply Forall_nil].
- eapply (region_kept_stack_aj trbsegs B); [exact HK1 | exact HJ | exact Usp_0 | lia | rewrite FFS; replace ASTACK with 16384 by reflexivity; lia | lia | lia | lia].
- apply (region_kept_val trbsegs E0 _ _ A_GOT_shadow 8 A_shadow_glob);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot1a) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot1) | lia].
- apply (region_kept_val trbsegs E0 _ _ A_shadow_glob 8 SHADOW_OFF);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell1a) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell1) | lia].
- eapply (region_kept_block_aj trbsegs B); [exact HK1 | rewrite A10_0; apply unsigned_lit_small; clear - Hc4096 Hcceil C1; lia | exact Hinc0 | lia
| change (req_size CHT_SIZE) with 48; unfold CHT_SIZE; lia | lia | ].
intros a Ha [Hb0 Hb].
pose proof (rg_sep_head_in B LAWS ly0 S0 W0 _ _ (c, CHT_SIZE) _ (f, nf) HARc0 HPerm0
ltac:(apply in_app_iff; left; exact (rg_optb_in _ _ Hb0))) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. change (req_size CHT_SIZE) with 48 in Hd. unfold CHT_SIZE in Ha. clear - Hd Ha Hb. lia. }
clear HS. rewrite <- restrict_mkst_fx in HSn. rename HSn into HS.
remember (havoc E0 40 (map (getr regs1) CLOB)) as E1 eqn:HE1 in HS.
assert (OLD1 : forall n, (n < 40)%nat -> ew E1 n = ew E0 n) by (intros n Hn; rewrite HE1; apply YO3v.ew_havoc_old; exact Hn).
assert (HAE_1 : env_agree 32 (Ereg regs (fc_extra f h u p x)) E1) by (rewrite HE1; apply env_agree_havoc_ge; [cbv; lia | exact HAE_0]).
clear HE1.
assert (A1_1 : ew E1 1 = getr regs 1) by (rewrite OLD1 by (cbv; lia); exact A1_0).
assert (A3_1 : ew E1 3 = getr regs 3) by (rewrite OLD1 by (cbv; lia); exact A3_0).
assert (A4_1 : ew E1 4 = getr regs 4) by (rewrite OLD1 by (cbv; lia); exact A4_0).
assert (A10_1 : ew E1 10 = Z_to_bv 64 c) by (rewrite OLD1 by (cbv; lia); exact A10_0).
assert (A32_1 : ew E1 32 = Z_to_bv 64 f) by (rewrite OLD1 by (cbv; lia); exact A32_0).
assert (A33_1 : ew E1 33 = Z_to_bv 64 h) by (rewrite OLD1 by (cbv; lia); exact A33_0).
assert (A34_1 : ew E1 34 = Z_to_bv 64 u) by (rewrite OLD1 by (cbv; lia); exact A34_0).
assert (A35_1 : ew E1 35 = Z_to_bv 64 SB) by (rewrite OLD1 by (cbv; lia); exact A35_0).
assert (A36_1 : ew E1 36 = Z_to_bv 64 p) by (rewrite OLD1 by (cbv; lia); exact A36_0).
assert (A37_1 : ew E1 37 = Z_to_bv 64 x) by (rewrite OLD1 by (cbv; lia); exact A37_0).
assert (Usp_1 : bv_unsigned (ew E1 2) = spZ regs) by (rewrite OLD1 by (cbv; lia); exact Usp_0).
shok_auto_with SHOK Bx E1 (mrestrict (w_H W1) mem1) fc_SH
ltac:(apply (shent_ok_of_block trbsegs B LAWS ly1 S1 W1 mem1 md1 E1 Bx 10 c CHT_SIZE 0 CHT_SIZE HAR1 Hinc1);
[ unfold U, Bx; cbn [sv_denot]; rewrite A35_1, Z.add_0_r, Z_to_bv_bv_unsigned; rewrite unsigned_lit_small by (unfold SB; lia); reflexivity
| unfold U; cbn [sv_denot]; rewrite A10_1, Z.add_0_r, Z_to_bv_bv_unsigned; rewrite unsigned_lit_small by (clear - Hc4096 Hcceil C1; lia); reflexivity
| lia | change (req_size CHT_SIZE) with 48; unfold CHT_SIZE; lia ]).
aj_run_tok trbtbl_lib_ok HS HJ SHOK Bspan. { awr_ok_tac. exact Usp_1. }
assert (HU2 : In [pc_free_ra0 Trb_code; 0x84f6c] (as_universe B)) by (rewrite (tl_universe B TL); apply memZL_In; vm_compute; reflexivity).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev1 & _).
pose proof (proj1 HJ) as HARc1.
lazymatch goal with |- SRr _ _ (mkCfg ?ms ?mdc) _ =>
rreg HS (2%bv : bv 5) R2; rreg HS (10%bv : bv 5) R10; rreg HS (3%bv : bv 5) R3; rreg HS (4%bv : bv 5) R4;
rreg HS (1%bv : bv 5) R1; rreg HS (8%bv : bv 5) R8;
eapply SRr_bind;
[ eapply (rg_aj_free_opt B LAWS Hsegs errno_low ML AFREE W1 E1 _ ms TFREECHT_STK (spZ regs) _ ly0 S0 W0 mem0 md0 [] ly1 S1 _ _
h nh (-32) (ew E1 2) (Z_to_bv 64 0x84f6c) [] ((c, CHT_SIZE) :: optb u nu ++ optb p np ++ optb x nx ++ rest));
[ exact HS | rewrite HBcode; reflexivity | reflexivity | exact HJ
| eapply Permutation_trans; [exact HPerm1 | apply Permutation_middle]
| rewrite R10, A33_1; reflexivity
| exact (st_ok_restrict_reg trbsegs (w_H W1) E1 _ _ 2%bv HS)
| reflexivity | exact Usp_1 | reflexivity | lia | rewrite FFS; replace ASTACK with 16384 by reflexivity; lia
| rewrite R3, A3_1; exact Hgp | rewrite R4, A4_1; exact Htp
| exact R1 | vm_compute; reflexivity | rewrite HEVC in Hev; clear - Hev Hnev1; lia
| eapply (achain_chain_pre ly1 _ (spZ regs - 32) c []);
[ apply achain_low; clear - Hcceil; lia
| change (spZ (ms_regs ms)) with (bv_unsigned (getr (ms_regs ms) 2)); rewrite R2, unsigned_lit_small by lia; lia
| unfold s0Z; rewrite R8, A10_1; apply unsigned_lit_small; clear - Hc4096 Hcceil C1; lia
| unfold raZ; rewrite R1; rewrite unsigned_lit_small by lia; lia ]
| rewrite call_trace_nil; unfold raZ; rewrite R1, unsigned_lit_small by lia; rewrite HBcode; cbn; exact HU2
| intros Hb0 _ i Hi; apply (inFP_ablocks_fp _ h nh i); [right; apply in_app_iff; right; apply in_app_iff; left; exact (rg_optb_in _ _ Hb0) | exact Hi] ]
| ]
end.
clear HJ SHOK R2 R10 R3 R4 R1 R8.
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HP2 & HPerm2 & Hfrs2 & HK2).
pose proof (proj1 HJ) as HAR2.
destruct (al_const _ _ LAWS _ _ _ _ _ HARc1) as (Kcell2a & _ & Kgot2a & _). rewrite HBgot, HBcell in Kgot2a. rewrite HBcell in Kcell2a.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR2) as (Kcell2 & _ & Kgot2 & _). rewrite HBgot, HBcell in Kgot2. rewrite HBcell in Kcell2.
assert (Hinc2 : In (c, CHT_SIZE) (ablocks B ly2 S2)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm2|]. left. reflexivity. }
jafter_call_keep HS 56%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2; 3]%nat HSn.
match type of HSn with ?t -> _ => assert (HRK : t); [|specialize (HSn HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | apply Forall_nil].
- eapply (region_kept_stack_aj trbsegs B); [exact HK2 | exact HJ | exact Usp_1 | lia | rewrite FFS; replace ASTACK with 16384 by reflexivity; lia | lia | lia | lia].
- apply (region_kept_val trbsegs E1 _ _ A_GOT_shadow 8 A_shadow_glob);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot2a) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot2) | lia].
- apply (region_kept_val trbsegs E1 _ _ A_shadow_glob 8 SHADOW_OFF);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell2a) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell2) | lia].
- eapply (region_kept_block_aj trbsegs B); [exact HK2 | rewrite A10_1; apply unsigned_lit_small; clear - Hc4096 Hcceil C1; lia | exact Hinc1 | lia
| change (req_size CHT_SIZE) with 48; unfold CHT_SIZE; lia | lia | ].
intros a Ha [Hb0 Hb].
pose proof (rg_sep_head_in B LAWS ly1 S1 W1 _ _ (c, CHT_SIZE) _ (h, nh) HARc1 HPerm1
ltac:(apply in_app_iff; left; exact (rg_optb_in _ _ Hb0))) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. change (req_size CHT_SIZE) with 48 in Hd. unfold CHT_SIZE in Ha. clear - Hd Ha Hb. lia. }
clear HS. rewrite <- restrict_mkst_fx in HSn. rename HSn into HS.
remember (havoc E1 56 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
assert (OLD2 : forall n, (n < 56)%nat -> ew E2 n = ew E1 n) by (intros n Hn; rewrite HE2; apply YO3v.ew_havoc_old; exact Hn).
assert (HAE_2 : env_agree 32 (Ereg regs (fc_extra f h u p x)) E2) by (rewrite HE2; apply env_agree_havoc_ge; [cbv; lia | exact HAE_1]).
clear HE2.
assert (A1_2 : ew E2 1 = getr regs 1) by (rewrite OLD2 by (cbv; lia); exact A1_1).
assert (A3_2 : ew E2 3 = getr regs 3) by (rewrite OLD2 by (cbv; lia); exact A3_1).
assert (A4_2 : ew E2 4 = getr regs 4) by (rewrite OLD2 by (cbv; lia); exact A4_1).
assert (A10_2 : ew E2 10 = Z_to_bv 64 c) by (rewrite OLD2 by (cbv; lia); exact A10_1).
assert (A32_2 : ew E2 32 = Z_to_bv 64 f) by (rewrite OLD2 by (cbv; lia); exact A32_1).
assert (A33_2 : ew E2 33 = Z_to_bv 64 h) by (rewrite OLD2 by (cbv; lia); exact A33_1).
assert (A34_2 : ew E2 34 = Z_to_bv 64 u) by (rewrite OLD2 by (cbv; lia); exact A34_1).
assert (A35_2 : ew E2 35 = Z_to_bv 64 SB) by (rewrite OLD2 by (cbv; lia); exact A35_1).
assert (A36_2 : ew E2 36 = Z_to_bv 64 p) by (rewrite OLD2 by (cbv; lia); exact A36_1).
assert (A37_2 : ew E2 37 = Z_to_bv 64 x) by (rewrite OLD2 by (cbv; lia); exact A37_1).
assert (Usp_2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite OLD2 by (cbv; lia); exact Usp_1).
shok_auto_with SHOK Bx E2 (mrestrict (w_H W2) mem2) fc_SH
ltac:(apply (shent_ok_of_block trbsegs B LAWS ly2 S2 W2 mem2 md2 E2 Bx 10 c CHT_SIZE 0 CHT_SIZE HAR2 Hinc2);
[ unfold U, Bx; cbn [sv_denot]; rewrite A35_2, Z.add_0_r, Z_to_bv_bv_unsigned; rewrite unsigned_lit_small by (unfold SB; lia); reflexivity
| unfold U; cbn [sv_denot]; rewrite A10_2, Z.add_0_r, Z_to_bv_bv_unsigned; rewrite unsigned_lit_small by (clear - Hc4096 Hcceil C1; lia); reflexivity
| lia | change (req_size CHT_SIZE) with 48; unfold CHT_SIZE; lia ]).
aj_run_tok trbtbl_lib_ok HS HJ SHOK Bspan. { awr_ok_tac. exact Usp_2. }
assert (HU3 : In [pc_free_ra0 Trb_code; 0x84f88] (as_universe B)) by (rewrite (tl_universe B TL); apply memZL_In; vm_compute; reflexivity).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev2 & _).
pose proof (proj1 HJ) as HARc2.
lazymatch goal with |- SRr _ _ (mkCfg ?ms ?mdc) _ =>
rreg HS (2%bv : bv 5) R2; rreg HS (10%bv : bv 5) R10; rreg HS (3%bv : bv 5) R3; rreg HS (4%bv : bv 5) R4;
rreg HS (1%bv : bv 5) R1; rreg HS (8%bv : bv 5) R8;
eapply SRr_bind;
[ eapply (rg_aj_free_opt B LAWS Hsegs errno_low ML AFREE W2 E2 _ ms TFREECHT_STK (spZ regs) _ ly0 S0 W0 mem0 md0 [] ly2 S2 _ _
u nu (-32) (ew E2 2) (Z_to_bv 64 0x84f88) [] ((c, CHT_SIZE) :: optb p np ++ optb x nx ++ rest));
[ exact HS | rewrite HBcode; reflexivity | reflexivity | exact HJ
| eapply Permutation_trans; [exact HPerm2 | apply Permutation_middle]
| rewrite R10, A34_2; reflexivity
| exact (st_ok_restrict_reg trbsegs (w_H W2) E2 _ _ 2%bv HS)
| reflexivity | exact Usp_2 | reflexivity | lia | rewrite FFS; replace ASTACK with 16384 by reflexivity; lia
| rewrite R3, A3_2; exact Hgp | rewrite R4, A4_2; exact Htp
| exact R1 | vm_compute; reflexivity | rewrite HEVC in Hev; clear - Hev Hnev2; lia
| eapply (achain_chain_pre ly2 _ (spZ regs - 32) c []);
[ apply achain_low; clear - Hcceil; lia
| change (spZ (ms_regs ms)) with (bv_unsigned (getr (ms_regs ms) 2)); rewrite R2, unsigned_lit_small by lia; lia
| unfold s0Z; rewrite R8, A10_2; apply unsigned_lit_small; clear - Hc4096 Hcceil C1; lia
| unfold raZ; rewrite R1; rewrite unsigned_lit_small by lia; lia ]
| rewrite call_trace_nil; unfold raZ; rewrite R1, unsigned_lit_small by lia; rewrite HBcode; cbn; exact HU3
| intros Hb0 _ i Hi; apply (inFP_ablocks_fp _ u nu i); [right; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; exact (rg_optb_in _ _ Hb0) | exact Hi] ]
| ]
end.
clear HJ SHOK R2 R10 R3 R4 R1 R8.
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ & HP3 & HPerm3 & Hfrs3 & HK3).
pose proof (proj1 HJ) as HAR3.
destruct (al_const _ _ LAWS _ _ _ _ _ HARc2) as (Kcell3a & _ & Kgot3a & _). rewrite HBgot, HBcell in Kgot3a. rewrite HBcell in Kcell3a.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR3) as (Kcell3 & _ & Kgot3 & _). rewrite HBgot, HBcell in Kgot3. rewrite HBcell in Kcell3.
assert (Hinc3 : In (c, CHT_SIZE) (ablocks B ly3 S3)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]. left. reflexivity. }
jafter_call_keep HS 72%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0; 1; 2; 3]%nat HSn.
match type of HSn with ?t -> _ => assert (HRK : t); [|specialize (HSn HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | apply Forall_nil].
- eapply (region_kept_stack_aj trbsegs B); [exact HK3 | exact HJ | exact Usp_2 | lia | rewrite FFS; replace ASTACK with 16384 by reflexivity; lia | lia | lia | lia].
- apply (region_kept_val trbsegs E2 _ _ A_GOT_shadow 8 A_shadow_glob);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot3a) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot3) | lia].
- apply (region_kept_val trbsegs E2 _ _ A_shadow_glob 8 SHADOW_OFF);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell3a) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell3) | lia].
- eapply (region_kept_block_aj trbsegs B); [exact HK3 | rewrite A10_2; apply unsigned_lit_small; clear - Hc4096 Hcceil C1; lia | exact Hinc2 | lia
| change (req_size CHT_SIZE) with 48; unfold CHT_SIZE; lia | lia | ].
intros a Ha [Hb0 Hb].
pose proof (rg_sep_head_in B LAWS ly2 S2 W2 _ _ (c, CHT_SIZE) _ (u, nu) HARc2 HPerm2
ltac:(apply in_app_iff; left; exact (rg_optb_in _ _ Hb0))) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. change (req_size CHT_SIZE) with 48 in Hd. unfold CHT_SIZE in Ha. clear - Hd Ha Hb. lia. }
clear HS. rewrite <- restrict_mkst_fx in HSn. rename HSn into HS.
remember (havoc E2 72 (map (getr regs3) CLOB)) as E3 eqn:HE3 in HS.
assert (OLD3 : forall n, (n < 72)%nat -> ew E3 n = ew E2 n) by (intros n Hn; rewrite HE3; apply YO3v.ew_havoc_old; exact Hn).
assert (HAE_3 : env_agree 32 (Ereg regs (fc_extra f h u p x)) E3) by (rewrite HE3; apply env_agree_havoc_ge; [cbv; lia | exact HAE_2]).
clear HE3.
assert (A1_3 : ew E3 1 = getr regs 1) by (rewrite OLD3 by (cbv; lia); exact A1_2).
assert (A3_3 : ew E3 3 = getr regs 3) by (rewrite OLD3 by (cbv; lia); exact A3_2).
assert (A4_3 : ew E3 4 = getr regs 4) by (rewrite OLD3 by (cbv; lia); exact A4_2).
assert (A10_3 : ew E3 10 = Z_to_bv 64 c) by (rewrite OLD3 by (cbv; lia); exact A10_2).
assert (A32_3 : ew E3 32 = Z_to_bv 64 f) by (rewrite OLD3 by (cbv; lia); exact A32_2).
assert (A33_3 : ew E3 33 = Z_to_bv 64 h) by (rewrite OLD3 by (cbv; lia); exact A33_2).
assert (A34_3 : ew E3 34 = Z_to_bv 64 u) by (rewrite OLD3 by (cbv; lia); exact A34_2).
assert (A35_3 : ew E3 35 = Z_to_bv 64 SB) by (rewrite OLD3 by (cbv; lia); exact A35_2).
assert (A36_3 : ew E3 36 = Z_to_bv 64 p) by (rewrite OLD3 by (cbv; lia); exact A36_2).
assert (A37_3 : ew E3 37 = Z_to_bv 64 x) by (rewrite OLD3 by (cbv; lia); exact A37_2).
assert (Usp_3 : bv_unsigned (ew E3 2) = spZ regs) by (rewrite OLD3 by (cbv; lia); exact Usp_2).
shok_auto_with SHOK Bx E3 (mrestrict (w_H W3) mem3) fc_SH
ltac:(apply (shent_ok_of_block trbsegs B LAWS ly3 S3 W3 mem3 md3 E3 Bx 10 c CHT_SIZE 0 CHT_SIZE HAR3 Hinc3);
[ unfold U, Bx; cbn [sv_denot]; rewrite A35_3, Z.add_0_r, Z_to_bv_bv_unsigned; rewrite unsigned_lit_small by (unfold SB; lia); reflexivity
| unfold U; cbn [sv_denot]; rewrite A10_3, Z.add_0_r, Z_to_bv_bv_unsigned; rewrite unsigned_lit_small by (clear - Hc4096 Hcceil C1; lia); reflexivity
| lia | change (req_size CHT_SIZE) with 48; unfold CHT_SIZE; lia ]).
aj_run_tok trbtbl_lib_ok HS HJ SHOK Bspan. { awr_ok_tac. exact Usp_3. }
assert (HU4 : In [pc_free_ra0 Trb_code; 0x84fa4] (as_universe B)) by (rewrite (tl_universe B TL); apply memZL_In; vm_compute; reflexivity).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
pose proof (proj1 HJ) as HARc3.
lazymatch goal with |- SRr _ _ (mkCfg ?ms ?mdc) _ =>
rreg HS (2%bv : bv 5) R2; rreg HS (10%bv : bv 5) R10; rreg HS (3%bv : bv 5) R3; rreg HS (4%bv : bv 5) R4;
rreg HS (1%bv : bv 5) R1; rreg HS (8%bv : bv 5) R8;
eapply SRr_bind;
[ eapply (rg_aj_free_opt B LAWS Hsegs errno_low ML AFREE W3 E3 _ ms TFREECHT_STK (spZ regs) _ ly0 S0 W0 mem0 md0 [] ly3 S3 _ _
p np (-32) (ew E3 2) (Z_to_bv 64 0x84fa4) [] ((c, CHT_SIZE) :: optb x nx ++ rest));
[ exact HS | rewrite HBcode; reflexivity | reflexivity | exact HJ
| eapply Permutation_trans; [exact HPerm3 | apply Permutation_middle]
| rewrite R10, A36_3; reflexivity
| exact (st_ok_restrict_reg trbsegs (w_H W3) E3 _ _ 2%bv HS)
| reflexivity | exact Usp_3 | reflexivity | lia | rewrite FFS; replace ASTACK with 16384 by reflexivity; lia
| rewrite R3, A3_3; exact Hgp | rewrite R4, A4_3; exact Htp
| exact R1 | vm_compute; reflexivity | rewrite HEVC in Hev; clear - Hev Hnev3; lia
| eapply (achain_chain_pre ly3 _ (spZ regs - 32) c []);
[ apply achain_low; clear - Hcceil; lia
| change (spZ (ms_regs ms)) with (bv_unsigned (getr (ms_regs ms) 2)); rewrite R2, unsigned_lit_small by lia; lia
| unfold s0Z; rewrite R8, A10_3; apply unsigned_lit_small; clear - Hc4096 Hcceil C1; lia
| unfold raZ; rewrite R1; rewrite unsigned_lit_small by lia; lia ]
| rewrite call_trace_nil; unfold raZ; rewrite R1, unsigned_lit_small by lia; rewrite HBcode; cbn; exact HU4
| intros Hb0 _ i Hi; apply (inFP_ablocks_fp _ p np i); [right; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; exact (rg_optb_in _ _ Hb0) | exact Hi] ]
| ]
end.
clear HJ SHOK R2 R10 R3 R4 R1 R8.
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ & HP4 & HPerm4 & Hfrs4 & HK4).
pose proof (proj1 HJ) as HAR4.
destruct (al_const _ _ LAWS _ _ _ _ _ HARc3) as (Kcell4a & _ & Kgot4a & _). rewrite HBgot, HBcell in Kgot4a. rewrite HBcell in Kcell4a.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR4) as (Kcell4 & _ & Kgot4 & _). rewrite HBgot, HBcell in Kgot4. rewrite HBcell in Kcell4.
assert (Hinc4 : In (c, CHT_SIZE) (ablocks B ly4 S4)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]. left. reflexivity. }
jafter_call_keep HS 88%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0; 1; 2; 3]%nat HSn.
match type of HSn with ?t -> _ => assert (HRK : t); [|specialize (HSn HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | apply Forall_nil].
- eapply (region_kept_stack_aj trbsegs B); [exact HK4 | exact HJ | exact Usp_3 | lia | rewrite FFS; replace ASTACK with 16384 by reflexivity; lia | lia | lia | lia].
- apply (region_kept_val trbsegs E3 _ _ A_GOT_shadow 8 A_shadow_glob);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot4a) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot4) | lia].
- apply (region_kept_val trbsegs E3 _ _ A_shadow_glob 8 SHADOW_OFF);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell4a) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell4) | lia].
- eapply (region_kept_block_aj trbsegs B); [exact HK4 | rewrite A10_3; apply unsigned_lit_small; clear - Hc4096 Hcceil C1; lia | exact Hinc3 | lia
| change (req_size CHT_SIZE) with 48; unfold CHT_SIZE; lia | lia | ].
intros a Ha [Hb0 Hb].
pose proof (rg_sep_head_in B LAWS ly3 S3 W3 _ _ (c, CHT_SIZE) _ (p, np) HARc3 HPerm3
ltac:(apply in_app_iff; left; exact (rg_optb_in _ _ Hb0))) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. change (req_size CHT_SIZE) with 48 in Hd. unfold CHT_SIZE in Ha. clear - Hd Ha Hb. lia. }
clear HS. rewrite <- restrict_mkst_fx in HSn. rename HSn into HS.
remember (havoc E3 88 (map (getr regs4) CLOB)) as E4 eqn:HE4 in HS.
assert (OLD4 : forall n, (n < 88)%nat -> ew E4 n = ew E3 n) by (intros n Hn; rewrite HE4; apply YO3v.ew_havoc_old; exact Hn).
assert (HAE_4 : env_agree 32 (Ereg regs (fc_extra f h u p x)) E4) by (rewrite HE4; apply env_agree_havoc_ge; [cbv; lia | exact HAE_3]).
clear HE4.
assert (A1_4 : ew E4 1 = getr regs 1) by (rewrite OLD4 by (cbv; lia); exact A1_3).
assert (A3_4 : ew E4 3 = getr regs 3) by (rewrite OLD4 by (cbv; lia); exact A3_3).
assert (A4_4 : ew E4 4 = getr regs 4) by (rewrite OLD4 by (cbv; lia); exact A4_3).
assert (A10_4 : ew E4 10 = Z_to_bv 64 c) by (rewrite OLD4 by (cbv; lia); exact A10_3).
assert (A32_4 : ew E4 32 = Z_to_bv 64 f) by (rewrite OLD4 by (cbv; lia); exact A32_3).
assert (A33_4 : ew E4 33 = Z_to_bv 64 h) by (rewrite OLD4 by (cbv; lia); exact A33_3).
assert (A34_4 : ew E4 34 = Z_to_bv 64 u) by (rewrite OLD4 by (cbv; lia); exact A34_3).
assert (A35_4 : ew E4 35 = Z_to_bv 64 SB) by (rewrite OLD4 by (cbv; lia); exact A35_3).
assert (A36_4 : ew E4 36 = Z_to_bv 64 p) by (rewrite OLD4 by (cbv; lia); exact A36_3).
assert (A37_4 : ew E4 37 = Z_to_bv 64 x) by (rewrite OLD4 by (cbv; lia); exact A37_3).
assert (Usp_4 : bv_unsigned (ew E4 2) = spZ regs) by (rewrite OLD4 by (cbv; lia); exact Usp_3).
shok_auto_with SHOK Bx E4 (mrestrict (w_H W4) mem4) fc_SH
ltac:(apply (shent_ok_of_block trbsegs B LAWS ly4 S4 W4 mem4 md4 E4 Bx 10 c CHT_SIZE 0 CHT_SIZE HAR4 Hinc4);
[ unfold U, Bx; cbn [sv_denot]; rewrite A35_4, Z.add_0_r, Z_to_bv_bv_unsigned; rewrite unsigned_lit_small by (unfold SB; lia); reflexivity
| unfold U; cbn [sv_denot]; rewrite A10_4, Z.add_0_r, Z_to_bv_bv_unsigned; rewrite unsigned_lit_small by (clear - Hc4096 Hcceil C1; lia); reflexivity
| lia | change (req_size CHT_SIZE) with 48; unfold CHT_SIZE; lia ]).
aj_run_tok trbtbl_lib_ok HS HJ SHOK Bspan. { awr_ok_tac. exact Usp_4. }
assert (HU5 : In [pc_free_ra0 Trb_code; 0x84fc0] (as_universe B)) by (rewrite (tl_universe B TL); apply memZL_In; vm_compute; reflexivity).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev4 & _).
pose proof (proj1 HJ) as HARc4.
lazymatch goal with |- SRr _ _ (mkCfg ?ms ?mdc) _ =>
rreg HS (2%bv : bv 5) R2; rreg HS (10%bv : bv 5) R10; rreg HS (3%bv : bv 5) R3; rreg HS (4%bv : bv 5) R4;
rreg HS (1%bv : bv 5) R1; rreg HS (8%bv : bv 5) R8;
eapply SRr_bind;
[ eapply (rg_aj_free_opt B LAWS Hsegs errno_low ML AFREE W4 E4 _ ms TFREECHT_STK (spZ regs) _ ly0 S0 W0 mem0 md0 [] ly4 S4 _ _
x nx (-32) (ew E4 2) (Z_to_bv 64 0x84fc0) [] ((c, CHT_SIZE) :: rest));
[ exact HS | rewrite HBcode; reflexivity | reflexivity | exact HJ
| eapply Permutation_trans; [exact HPerm4 | apply Permutation_middle]
| rewrite R10, A37_4; reflexivity
| exact (st_ok_restrict_reg trbsegs (w_H W4) E4 _ _ 2%bv HS)
| reflexivity | exact Usp_4 | reflexivity | lia | rewrite FFS; replace ASTACK with 16384 by reflexivity; lia
| rewrite R3, A3_4; exact Hgp | rewrite R4, A4_4; exact Htp
| exact R1 | vm_compute; reflexivity | rewrite HEVC in Hev; clear - Hev Hnev4; lia
| eapply (achain_chain_pre ly4 _ (spZ regs - 32) c []);
[ apply achain_low; clear - Hcceil; lia
| change (spZ (ms_regs ms)) with (bv_unsigned (getr (ms_regs ms) 2)); rewrite R2, unsigned_lit_small by lia; lia
| unfold s0Z; rewrite R8, A10_4; apply unsigned_lit_small; clear - Hc4096 Hcceil C1; lia
| unfold raZ; rewrite R1; rewrite unsigned_lit_small by lia; lia ]
| rewrite call_trace_nil; unfold raZ; rewrite R1, unsigned_lit_small by lia; rewrite HBcode; cbn; exact HU5
| intros Hb0 _ i Hi; apply (inFP_ablocks_fp _ x nx i); [right; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; exact (rg_optb_in _ _ Hb0) | exact Hi] ]
| ]
end.
clear HJ SHOK R2 R10 R3 R4 R1 R8.
cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ & HP5 & HPerm5 & Hfrs5 & HK5).
pose proof (proj1 HJ) as HAR5.
destruct (al_const _ _ LAWS _ _ _ _ _ HARc4) as (Kcell5a & _ & Kgot5a & _). rewrite HBgot, HBcell in Kgot5a. rewrite HBcell in Kcell5a.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR5) as (Kcell5 & _ & Kgot5 & _). rewrite HBgot, HBcell in Kgot5. rewrite HBcell in Kcell5.
assert (Hinc5 : In (c, CHT_SIZE) (ablocks B ly5 S5)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm5|]. left. reflexivity. }
jafter_call_keep HS 104%nat regs5 (mrestrict (w_H W5) mem5) HP5 [0; 1; 2; 3]%nat HSn.
match type of HSn with ?t -> _ => assert (HRK : t); [|specialize (HSn HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | apply Forall_nil].
- eapply (region_kept_stack_aj trbsegs B); [exact HK5 | exact HJ | exact Usp_4 | lia | rewrite FFS; replace ASTACK with 16384 by reflexivity; lia | lia | lia | lia].
- apply (region_kept_val trbsegs E4 _ _ A_GOT_shadow 8 A_shadow_glob);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot5a) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot5) | lia].
- apply (region_kept_val trbsegs E4 _ _ A_shadow_glob 8 SHADOW_OFF);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell5a) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell5) | lia].
- eapply (region_kept_block_aj trbsegs B); [exact HK5 | rewrite A10_4; apply unsigned_lit_small; clear - Hc4096 Hcceil C1; lia | exact Hinc4 | lia
| change (req_size CHT_SIZE) with 48; unfold CHT_SIZE; lia | lia | ].
intros a Ha [Hb0 Hb].
pose proof (rg_sep_head_in B LAWS ly4 S4 W4 _ _ (c, CHT_SIZE) _ (x, nx) HARc4 HPerm4
ltac:(apply in_app_iff; left; exact (rg_optb_in _ _ Hb0))) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. change (req_size CHT_SIZE) with 48 in Hd. unfold CHT_SIZE in Ha. clear - Hd Ha Hb. lia. }
clear HS. rewrite <- restrict_mkst_fx in HSn. rename HSn into HS.
remember (havoc E4 104 (map (getr regs5) CLOB)) as E5 eqn:HE5 in HS.
assert (OLD5 : forall n, (n < 104)%nat -> ew E5 n = ew E4 n) by (intros n Hn; rewrite HE5; apply YO3v.ew_havoc_old; exact Hn).
assert (HAE_5 : env_agree 32 (Ereg regs (fc_extra f h u p x)) E5) by (rewrite HE5; apply env_agree_havoc_ge; [cbv; lia | exact HAE_4]).
clear HE5.
assert (A1_5 : ew E5 1 = getr regs 1) by (rewrite OLD5 by (cbv; lia); exact A1_4).
assert (A3_5 : ew E5 3 = getr regs 3) by (rewrite OLD5 by (cbv; lia); exact A3_4).
assert (A4_5 : ew E5 4 = getr regs 4) by (rewrite OLD5 by (cbv; lia); exact A4_4).
assert (A10_5 : ew E5 10 = Z_to_bv 64 c) by (rewrite OLD5 by (cbv; lia); exact A10_4).
assert (A32_5 : ew E5 32 = Z_to_bv 64 f) by (rewrite OLD5 by (cbv; lia); exact A32_4).
assert (A33_5 : ew E5 33 = Z_to_bv 64 h) by (rewrite OLD5 by (cbv; lia); exact A33_4).
assert (A34_5 : ew E5 34 = Z_to_bv 64 u) by (rewrite OLD5 by (cbv; lia); exact A34_4).
assert (A35_5 : ew E5 35 = Z_to_bv 64 SB) by (rewrite OLD5 by (cbv; lia); exact A35_4).
assert (A36_5 : ew E5 36 = Z_to_bv 64 p) by (rewrite OLD5 by (cbv; lia); exact A36_4).
assert (A37_5 : ew E5 37 = Z_to_bv 64 x) by (rewrite OLD5 by (cbv; lia); exact A37_4).
assert (Usp_5 : bv_unsigned (ew E5 2) = spZ regs) by (rewrite OLD5 by (cbv; lia); exact Usp_4).
shok_auto_with SHOK Bx E5 (mrestrict (w_H W5) mem5) fc_SH
ltac:(apply (shent_ok_of_block trbsegs B LAWS ly5 S5 W5 mem5 md5 E5 Bx 10 c CHT_SIZE 0 CHT_SIZE HAR5 Hinc5);
[ unfold U, Bx; cbn [sv_denot]; rewrite A35_5, Z.add_0_r, Z_to_bv_bv_unsigned; rewrite unsigned_lit_small by (unfold SB; lia); reflexivity
| unfold U; cbn [sv_denot]; rewrite A10_5, Z.add_0_r, Z_to_bv_bv_unsigned; rewrite unsigned_lit_small by (clear - Hc4096 Hcceil C1; lia); reflexivity
| lia | change (req_size CHT_SIZE) with 48; unfold CHT_SIZE; lia ]).
aj_run_tok trbtbl_lib_ok HS HJ SHOK Bspan. { awr_ok_tac. exact Usp_5. }
rreg HS (10%bv : bv 5) R10. rreg HS (1%bv : bv 5) R1.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 340932 with (pc_wrap_free code) by (rewrite HBcode; reflexivity).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & Hk5 & _).
eapply SRr_mono.
{ eapply (fc_tail W0 ly0 S0 regs mem0 md0 ch c FPc rest); [exact HPRE | exact HU0 | exact Hev | exact HJ | lia | exact HPerm5 | | | |].
+ intros i Hi. apply (inFP_ablocks_fp _ c CHT_SIZE i); [left; reflexivity | exact Hi].
+ eapply (aregs_preserved_of_st_ok trbsegs _ E5 _ _ regs (fc_extra f h u p x) HS); [exact HAE_5 | vm_compute; reflexivity].
+ cbn [ms_regs]. rewrite R10, A10_5. reflexivity.
+ cbn [ms_regs]. rewrite R1, A1_5. reflexivity. }
cbv beta. intros W6 c6 _ (ly6 & S6 & regs6 & mem6 & md6 & -> & HJ6 & HP6 & HPerm6).
exists ly6, S6, regs6, mem6, md6. split; [reflexivity|]. split; [exact HJ6|]. split; [exact HP6 | exact HPerm6].
Qed.
End d.
End b.
