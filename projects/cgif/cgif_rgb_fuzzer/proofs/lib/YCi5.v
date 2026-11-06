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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0n YG0t YCi2.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI08 YI0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AFREE : afree_realizes trbsegs B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let errno_low := tl_env B TL.
Local Abbreviation code := (as_code B).
Definition Bx : sv := SOff 35 0.
Definition fdt_regions (leafv : Z) : smem :=
[ stack_region 32; got_region; bcell_region 35;
YQ0b.mkRegion (Some 10%nat) 0 NODE_SIZE 0 0
[YQ0b.mkChunk 0 (CVal 8 (SOff 32 0)); YQ0b.mkChunk 8 (CVal 8 (SOff 33 0)); YQ0b.mkChunk 50 (CVal 1 (SLit leafv))] ].
Definition fdt_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 4096 140737479966720 4);
(32%nat, mkAF 0 (2^64 - 1) 0); (33%nat, mkAF 0 (2^64 - 1) 0); (35%nat, mkAF SB SB 0) ] [] [].
Definition ss_fdt (leafv : Z) : sstate := mkSS A_free_decision_tree sr_atoms (fdt_regions leafv) None fdt_facts.
Definition fdt_SH : list shent := [ mkSHE 10 0 NODE_SIZE ].
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition fdt_extra (c0 c1 : Z) : list word := map (Z_to_bv 64) [c0; c1; 0; SB].
Definition fdt_null_regions : smem := [ stack_region 32; got_region; bcell_region 35 ].
Definition fdt_null_facts : facts := mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 0 0 0); (35%nat, mkAF SB SB 0) ] [] [].
Definition ss_fdt_null : sstate := mkSS A_free_decision_tree (sr_set sr_atoms 10%bv (SLit 0)) fdt_null_regions None fdt_null_facts.
Lemma fdt_entry : forall leafv STK W ly S regs mem md ch a c0 c1 rest,
afn_pre trbsegs B STK ly S W regs mem md ch -> 16416 <= STK ->
getr regs 10 = w64 a ->
Permutation (ablocks B ly S) ((a, NODE_SIZE) :: rest) ->
val_mem trbsegs (mrestrict (w_H W) mem) a 8 c0 -> val_mem trbsegs (mrestrict (w_H W) mem) (a + 8) 8 c1 ->
val_mem trbsegs (mrestrict (w_H W) mem) (a + 50) 1 leafv ->
0 <= c0 < 2 ^ 64 -> 0 <= c1 < 2 ^ 64 -> 0 <= leafv < 256 ->
st_ok trbsegs (Ereg regs (fdt_extra c0 c1)) (ss_fdt leafv)
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_free_decision_tree) mem (seg_rom trbsegs)))
/\ sh_ok trbsegs Bx fdt_SH (Ereg regs (fdt_extra c0 c1)) (mrestrict (w_H W) mem).
Proof.
intros leafv STK W ly S regs mem md ch a c0 c1 rest HPRE HSTK H10 HPerm M0 M8 M50 R0 R8 RL.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hina : In (a, NODE_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS ly S W mem md a NODE_SIZE HAR Hina) as (Ha16 & Ha4096 & Haceil & Hah_ia & _ & _). pose proof (proj1 Hah_ia) as Hah.
pose proof (blk_off_img _ _ _ _ _ _ a NODE_SIZE HAR Hina) as Hah_img.
change (req_size NODE_SIZE) with 56 in *.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Ereg regs (fdt_extra c0 c1)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 a) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (EX : forall j, ew E (32 + j) = nth j (fdt_extra c0 c1) (Z_to_bv 64 0)) by (intros j; subst E; apply ew_Ereg_extra).
pose proof (EX 0%nat) as E32. pose proof (EX 1%nat) as E33. pose proof (EX 3%nat) as E35.
cbn [Nat.add nth fdt_extra map] in E32, E33, E35. clear EX.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_fdt. apply (entry_st_ok_full trbsegs); change (Ereg regs (fdt_extra c0 c1)) with E.
+ apply regs_ok_Ereg.
+ vm_compute. reflexivity.
+ unfold fdt_regions, stack_region, got_region, bcell_region.
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
* rewrite (VB 10%nat a E10) by lia. unfold NODE_SIZE. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor]]].
-- apply (chunk_ok_val trbsegs E _ a 0 8 _ c0); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact M0].
-- apply (chunk_ok_val trbsegs E _ a 8 8 _ c1); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M8].
-- apply (chunk_ok_val trbsegs E _ a 50 1 _ leafv); [reflexivity | zside | zside | exact M50].
+ apply pairwise_disjoint_of_extents. unfold fdt_regions, stack_region, got_region, bcell_region, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi]. rewrite (VB 10%nat a E10) by lia. cbn [base_val]. rewrite Usp.
unfold A_GOT_shadow, A_shadow_glob, NODE_SIZE.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Haceil Hah Hah_img Ha4096 C1 C3 HSTK Hstk0. clear. unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [fdt_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, E33, E35, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Haceil Hah Hah_img Ha4096 Ha16 Hal16 R0 R8 C1 C3 HSTK Hstk0. clear. unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, fdt_SH. constructor; [|constructor].
apply (shent_ok_of_block trbsegs B LAWS ly S W mem md E Bx 10 a NODE_SIZE 0 NODE_SIZE HAR Hina).
* unfold U, Bx. cbn [sv_denot]. rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
* unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
* lia.
* change (req_size NODE_SIZE) with 56. unfold NODE_SIZE. lia.
Qed.
Lemma fdt_entry_null : forall STK W ly S regs mem md ch,
afn_pre trbsegs B STK ly S W regs mem md ch -> 16416 <= STK ->
getr regs 10 = w64 0 ->
st_ok trbsegs (Ereg regs (fdt_extra 0 0)) ss_fdt_null
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_free_decision_tree) mem (seg_rom trbsegs)))
/\ sh_ok trbsegs Bx [] (Ereg regs (fdt_extra 0 0)) (mrestrict (w_H W) mem).
Proof.
intros STK W ly S regs mem md ch HPRE HSTK H10.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Ereg regs (fdt_extra 0 0)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 0) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E35 : ew E 35 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
split; [|constructor].
unfold ss_fdt_null. apply (entry_st_ok_full trbsegs); change (Ereg regs (fdt_extra 0 0)) with E.
+ apply regs_ok_rereg; [apply regs_ok_Ereg | reflexivity | rewrite H10; reflexivity].
+ vm_compute. reflexivity.
+ unfold fdt_null_regions, stack_region, got_region, bcell_region.
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
+ apply pairwise_disjoint_of_extents. unfold fdt_null_regions, stack_region, got_region, bcell_region, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi]. cbn [base_val]. rewrite Usp.
unfold A_GOT_shadow, A_shadow_glob.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 HSTK Hstk0. clear. unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [fdt_null_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E35, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hal16 C1 C3 HSTK Hstk0. clear. unfold SB, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
repeat match goal with |- _ /\ _ => split end; lia.
Qed.
Lemma fdt_tail : forall STK EVT W ly S regs mem md ch a FP rest Wt regsT memT lyt St mdt kt,
afn_pre trbsegs B STK ly S W regs mem md ch -> 16416 <= STK ->
In (call_trace0 (pc_free_ra0 Trb_code) regs ch) (as_universe B) ->
vev St < VEV_MAX -> bud_le S St (EVT - 1) 0 0 0 ->
ajournal trbsegs B STK (spZ regs) FP ly S W mem md [] lyt St Wt memT mdt kt -> kt + 1 <= EVT ->
Permutation (ablocks B lyt St) ((a, NODE_SIZE) :: rest) ->
(forall i, 0 <= i < req_size NODE_SIZE -> inFP FP (a + i)) ->
aregs_preserved regs regsT -> getr regsT 10 = w64 a -> getr regsT 1 = getr regs 1 ->
SRr trbsegs Wt (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom trbsegs)) mdt)
(apost_base B STK FP regs ly S W mem md EVT (fun ly' S' W' regs' mem' md' => Permutation (ablocks B ly' S') rest /\ bud_le S S' EVT 0 0 0)).
Proof.
intros STK EVT W ly S regs mem md ch a FP rest Wt regsT memT lyt St mdt kt HPRE HSTK HU Hev HbT HJ Hkt HPermR HFPc HP Ha0 Hra1.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (HARt & Hly & _ & _ & _ & _ & Hnev & _ & G1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HinT : In (a, NODE_SIZE) (ablocks B lyt St)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPermR|]. left. reflexivity. }
assert (P2 : getr regsT 2 = getr regs 2) by (apply (HP 2); left; reflexivity).
assert (P3 : getr regsT 3 = getr regs 3) by (apply (HP 3); right; left; reflexivity).
assert (P4 : getr regsT 4 = getr regs 4) by (apply (HP 4); right; right; left; reflexivity).
assert (P8 : getr regsT 8 = getr regs 8) by (apply (HP 8); right; right; right; left; reflexivity).
eapply SRr_mono.
{ eapply (aj_free_atD trbsegs B LAWS trb_segs_low errno_low ML AFREE Wt regsT memT STK (spZ regs) _ ly S W mem md [] lyt St mdt kt
a NODE_SIZE 0 (getr regs 1) ch HJ HinT Ha0).
- unfold spZ. rewrite P2. lia.
- reflexivity. - lia. - replace ASTACK with 16384 by reflexivity. lia.
- rewrite P3; exact Hgp. - rewrite P4; exact Htp.
- exact Hra1. - exact Hra. - exact Hev.
- eapply (achain_chain_pre lyt _ (spZ regs) (s0Z regs) ch).
+ apply (achain_ly_top ly lyt). { destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & ET & _). exact ET. }
eapply (achain_kept ly _ _ (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia |].
intros x Hx. apply G1; lia.
+ change (spZ regsT) with (bv_unsigned (getr regsT 2)). rewrite P2. change (bv_unsigned (getr regs 2)) with (spZ regs). lia.
+ unfold s0Z. rewrite P8. reflexivity.
+ unfold raZ. rewrite Hra1. exact Hra4.
- unfold call_trace0, raZ in *. rewrite Hra1, HBcode. exact HU.
- intros _ i Hi. exact (HFPc i Hi). }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (l1' & l2' & Ebl' & Ebl2') & _ & Hd3 & _).
exists ly3, S3, regs3, mem3, md3. split; [reflexivity|].
split; [eapply (ajournal_mono_k trbsegs B); [exact HJ3 | lia]|].
split; [eapply aregs_preserved_trans; [exact HP | exact HP3]|].
split.
{ rewrite Ebl2'. apply Permutation_sym. apply (@Permutation_cons_app_inv _ _ l1' l2' (a, NODE_SIZE)). rewrite <- Ebl'.
apply Permutation_sym. exact HPermR. }
eapply bud_le_mono; [exact (bud_le_trans _ _ _ _ _ _ _ _ _ _ _ HbT Hd3) | lia | lia | lia | lia].
Qed.
Lemma fdt_stk_ge : forall d, 16416 <= FDT_STK (Z.of_nat d).
Proof. intros d. unfold FDT_STK. replace ASTACK with 16384 by reflexivity. lia. Qed.
Theorem trb_free_decision_treeV : tfree_tree_specV B.
Proof.
unfold tfree_tree_specV.
intros d ly S W regs mem md ch t. revert d ly S W regs mem md ch.
induction t as [|n|n l IHl r IHr]; intros d ly S W regs mem md ch rest Hh HPRE HCTX H10 Hat HPerm Hev.
-
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof (fdt_stk_ge d) as HSTK. set (STK := FDT_STK (Z.of_nat d)) in *. clearbody STK.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
cbn [troot] in H10. cbn [tree_blocks app] in HPerm. cbn [tree_blocks tree_nodes length Z.of_nat ablocks_fp map] in *.
destruct (fdt_entry_null STK W ly S regs mem md ch HPRE HSTK H10) as [HS SHOK].
pose proof (ajournal_init trbsegs B STK [] ly S W regs mem md ch HPRE) as HJ.
remember (Ereg regs (fdt_extra 0 0)) as E eqn:HE.
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (fdt_extra 0 0)) E) by (rewrite HE; split; [intros k Hk; reflexivity | reflexivity]).
clear HE.
unfold cfg_at. change (w64 A_free_decision_tree) with (Z_to_bv 64 A_free_decision_tree).
aj_run_tok trbtbl_lib_ok HS HJ SHOK Bspan.
{ eapply awr_ok_cons_stack; [reflexivity | exact Usp | cbn; clear - HSTK; lia | cbn; clear; lia |]. awr_ok_tac. }
rreg HS (1%bv : bv 5) R1.
eapply (SRr_ret_at trbsegs trbtbl_lib trbtbl_lib_ok Hwx W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. lazymatch goal with |- apost_base _ _ _ _ _ _ _ _ _ _ _ _ (mkCfg (mkst ?rr _ ?m _) ?d0) => exists ly, S, rr, m, d0 end.
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
split; [|split].
+ cbn [ms_mem]. apply (ajournal_materialize trbsegs B LAWS Hsegs). exact HJ.
+ eapply (aregs_preserved_of_st_ok trbsegs _ E _ _ regs (fdt_extra 0 0) HS); [exact HAE | vm_compute; reflexivity].
+ split; [exact HPerm | apply bud_le_refl].
-
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof (fdt_stk_ge d) as HSTK. set (STK := FDT_STK (Z.of_nat d)) in *. clearbody STK.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
cbn [troot] in H10. cbn [tree_blocks app] in HPerm. cbn [tree_nodes length] in Hev |- *. cbn [tree_blocks].
cbn [tree_at] in Hat. destruct Hat as (Hn0 & Hlen & c0 & c1 & Ho).
destruct (rg_node_fields _ _ c0 c1 n 1 Hlen Ho) as (V0 & RC0 & V8 & RC8 & V50 & RC50).
set (a := tn_addr n) in *.
destruct (fdt_entry 1 STK W ly S regs mem md ch a c0 c1 rest HPRE HSTK H10 HPerm V0 V8 V50 RC0 RC8 ltac:(lia)) as [HS SHOK].
assert (HU0 : In (call_trace0 (pc_free_ra0 Trb_code) regs ch) (as_universe B)).
{ rewrite (tl_universe B TL). exact (rg_trace0_of_ctx CTX_free_decision_tree Trb_universe (pc_free_ra0 Trb_code) regs ch ltac:(vm_compute; reflexivity) HCTX). }
pose proof (ajournal_init trbsegs B STK (ablocks_fp [(a, NODE_SIZE)]) ly S W regs mem md ch HPRE) as HJ.
remember (Ereg regs (fdt_extra c0 c1)) as E eqn:HE.
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 a) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (fdt_extra c0 c1)) E) by (rewrite HE; split; [intros k Hk; reflexivity | reflexivity]).
clear HE.
unfold cfg_at. change (w64 A_free_decision_tree) with (Z_to_bv 64 A_free_decision_tree).
aj_run_tok trbtbl_lib_ok HS HJ SHOK Bspan.
{ eapply awr_ok_cons_stack; [reflexivity | exact Usp | cbn; clear - HSTK; lia | cbn; clear; lia |]. awr_ok_tac. }
rreg HS (10%bv : bv 5) R10. rreg HS (1%bv : bv 5) R1.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 340932 with (pc_wrap_free code) by (rewrite HBcode; reflexivity).
eapply (fdt_tail STK _ W ly S regs mem md ch a _ rest W _ _ ly S _ 0 HPRE HSTK HU0);
[ apply (vev_lt_of_bud S S _ _ _ _ 0 0 0 0 Hev (bud_le_refl S)); clear; lia
| eapply bud_le_mono; [apply bud_le_refl | clear; lia ..]
| exact HJ | cbn; clear; lia | exact HPerm | | | |].
+ intros i Hi. apply (inFP_ablocks_fp _ a NODE_SIZE i); [left; reflexivity | exact Hi].
+ eapply (aregs_preserved_of_st_ok trbsegs _ _ _ _ regs (fdt_extra c0 c1) HS); [env_agree_chain HAE | vm_compute; reflexivity].
+ cbn [ms_regs]. rewrite R10, E10. reflexivity.
+ cbn [ms_regs]. rewrite R1, E1. reflexivity.
-
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
cbn [tree_height] in Hh. destruct d as [|d']; [exfalso; clear - Hh; lia|].
assert (Hhl : (tree_height l <= d')%nat) by (clear - Hh; lia).
assert (Hhr : (tree_height r <= d')%nat) by (clear - Hh; lia).
pose proof (fdt_stk_ge (Datatypes.S d')) as HSTK. pose proof (fdt_stk_ge d') as HSTK1g.
assert (HSTK1 : FDT_STK (Z.of_nat d') + 32 <= FDT_STK (Z.of_nat (Datatypes.S d'))) by (unfold FDT_STK; clear; lia).
set (STK := FDT_STK (Z.of_nat (Datatypes.S d'))) in *. clearbody STK.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
cbn [troot] in H10. cbn [tree_blocks app] in HPerm. rewrite <- app_assoc in HPerm.
cbn [tree_at] in Hat. destruct Hat as (Hn0 & Hlen & Ho & Hatl & Hatr).
destruct (rg_node_fields _ _ (troot l) (troot r) n 0 Hlen Ho) as (V0 & RC0 & V8 & RC8 & V50 & RC50).
set (a := tn_addr n) in *.
set (EVl := Z.of_nat (length (tree_nodes l))) in *. set (EVr := Z.of_nat (length (tree_nodes r))) in *.
assert (HEV : Z.of_nat (length (tree_nodes (TNode n l r))) = 1 + EVl + EVr).
{ cbn [tree_nodes length]. rewrite length_app. subst EVl EVr. lia. }
assert (HEVl0 : 0 <= EVl) by (subst EVl; lia). assert (HEVr0 : 0 <= EVr) by (subst EVr; lia).
rewrite HEV in Hev |- *.
set (FPn := ablocks_fp (tree_blocks (TNode n l r))).
assert (Hina : In (a, NODE_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS ly S W mem md a NODE_SIZE HAR Hina) as (Ha16 & Ha4096 & Haceil & _).
change (req_size NODE_SIZE) with 56 in Haceil.
assert (Hsub : forall x, In x (tree_blocks l ++ tree_blocks r) -> In x (ablocks B ly S)).
{ intros x Hx. eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. right. rewrite app_assoc. apply in_app_iff. left. exact Hx. }
destruct (fdt_entry 0 STK W ly S regs mem md ch a (troot l) (troot r) _ HPRE HSTK H10 HPerm V0 V8 V50 RC0 RC8 ltac:(lia)) as [HS SHOK].
assert (HU0 : In (call_trace0 (pc_free_ra0 Trb_code) regs ch) (as_universe B)).
{ rewrite (tl_universe B TL). exact (rg_trace0_of_ctx CTX_free_decision_tree Trb_universe (pc_free_ra0 Trb_code) regs ch ltac:(vm_compute; reflexivity) HCTX). }
pose proof (ajournal_init trbsegs B STK FPn ly S W regs mem md ch HPRE) as HJ.
remember (Ereg regs (fdt_extra (troot l) (troot r))) as E eqn:HE.
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 a) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 (troot l)) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (troot r)) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E35 : ew E 35 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (fdt_extra (troot l) (troot r))) E) by (rewrite HE; split; [intros k Hk; reflexivity | reflexivity]).
clear HE.
unfold cfg_at. change (w64 A_free_decision_tree) with (Z_to_bv 64 A_free_decision_tree).
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK Bspan 0x8534c.
{ eapply awr_ok_cons_stack; [reflexivity | exact Usp | cbn; clear - HSTK; lia | cbn; clear; lia |]. awr_ok_tac. }
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msA := msx) in * end.
rename HFr into HFr1. clear HF HG.
assert (KA1 : forall b sz, In (b, sz) (tree_blocks l ++ tree_blocks r) -> rg_blk_kept (w_H W) (w_H W) mem (ms_mem msA) b (req_size sz)).
{ intros b sz Hb. pose proof (Hsub _ Hb) as Hbx.
destruct (al_blocks _ _ LAWS ly S W mem md b sz HAR Hbx) as (_ & Hb4096 & Hbceil & _).
lazymatch type of HFr1 with frame_of ?Ef ?rs _ _ => apply (rg_blk_kept_frame Ef rs (w_H W) mem (ms_mem msA) b (req_size sz) HFr1) end.
intros x Hx. split; [clear - Hx Hb4096 Hbceil C1; lia|].
intros (rr & Hin & Hr). cbn [ss_mem ss_fdt fdt_regions] in Hin.
unfold stack_region, got_region, bcell_region in Hin. cbn [In] in Hin.
destruct Hin as [<- | [<- | [<- | [<- | []]]]]; unfold stack_region, got_region, bcell_region in Hr;
cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr; rewrite ?ew_ewset_other in Hr by (cbv; lia); try rewrite Usp in Hr;
clear - Hr Hx Hbceil Hceil Hslo Hstk0 HSTK; lia. }
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK Bspan A_free_decision_tree.
{ eapply awr_ok_cons_stack; [reflexivity | rewrite ?ew_ewset_other by (cbv; lia); exact Usp | cbn; clear - HSTK; lia | cbn; clear; lia |]. awr_ok_tac. }
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msB := msx) in * end.
rename HFr into HFr2. clear HF HG.
assert (KA2 : forall b sz, In (b, sz) (tree_blocks l ++ tree_blocks r) -> rg_blk_kept (w_H W) (w_H W) (ms_mem msA) (ms_mem msB) b (req_size sz)).
{ intros b sz Hb. pose proof (Hsub _ Hb) as Hbx.
destruct (al_blocks _ _ LAWS ly S W mem md b sz HAR Hbx) as (_ & Hb4096 & Hbceil & _).
lazymatch type of HFr2 with frame_of ?Ef ?rs _ _ => apply (rg_blk_kept_frame Ef rs (w_H W) (ms_mem msA) (ms_mem msB) b (req_size sz) HFr2) end.
intros x Hx. split; [clear - Hx Hb4096 Hbceil C1; lia|].
intros (rr & Hin & Hr). cbn [ss_mem ss_fdt fdt_regions] in Hin.
unfold stack_region, got_region, bcell_region in Hin. cbn [In] in Hin.
destruct Hin as [<- | [<- | [<- | [<- | []]]]]; unfold stack_region, got_region, bcell_region in Hr;
cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr; rewrite ?ew_ewset_other in Hr by (cbv; lia); try rewrite Usp in Hr;
clear - Hr Hx Hbceil Hceil Hslo Hstk0 HSTK; lia. }
assert (Hatl1 : tree_at trbsegs (mrestrict (w_H W) (ms_mem msB)) l).
{ apply (rg_tree_at_kept (w_H W) (w_H W) mem (ms_mem msB) l Hatl). intros b sz Hb.
eapply rg_blk_kept_trans; [apply KA1 | apply KA2]; apply in_app_iff; left; exact Hb. }
assert (HPl : Permutation (ablocks B ly S) (tree_blocks l ++ (a, NODE_SIZE) :: tree_blocks r ++ rest)).
{ eapply Permutation_trans; [exact HPerm|]. apply Permutation_middle. }
pose proof (proj1 HJ) as HARc.
lazymatch goal with |- SRr _ _ (mkCfg ?ms ?mdc) _ =>
lazymatch type of HS with st_ok _ ?Ex ?ssX _ =>
assert (UspX : bv_unsigned (ew Ex 2) = spZ regs) by (rewrite ?ew_ewset_other by (cbv; lia); exact Usp);
rreg HS (2%bv : bv 5) R2; rreg HS (10%bv : bv 5) R10; rreg HS (3%bv : bv 5) R3; rreg HS (4%bv : bv 5) R4;
rreg HS (1%bv : bv 5) R1; rreg HS (8%bv : bv 5) R8;
eapply SRr_bind;
[ eapply (aj_call trbsegs B LAWS Hsegs W Ex ssX ms STK (spZ regs) _ ly S W mem md [] ly S mdc 0
(FDT_STK (Z.of_nat d')) (ablocks_fp (tree_blocks l)) EVl (-32) (ew Ex 2) (Z_to_bv 64 0x85350) []
(fun ly2 S2 W2 regs2 mem2 md2 => Permutation (ablocks B ly2 S2) ((a, NODE_SIZE) :: tree_blocks r ++ rest) /\ bud_le S S2 EVl 0 0 0) HS eq_refl HJ);
[ first [ exact (st_ok_restrict_reg trbsegs (w_H W) Ex _ _ 2%bv HS) | match goal with |- ?gg => idtac "AJ1" gg end ]
| first [ reflexivity | idtac "AJ2" ]
| first [ exact UspX | idtac "AJ3" ]
| first [ reflexivity | idtac "AJ4" ]
| first [ lia | idtac "AJ5" ]
| first [ clear - HSTK1g; lia | idtac "AJ6" ]
| first [ clear - HSTK1; lia | match goal with |- ?gg => idtac "AJ7" gg end ]
| first [ rewrite R3, E3; exact Hgp | idtac "AJ8" ]
| first [ rewrite R4, E4; exact Htp | idtac "AJ9" ]
| first [ exact R1 | match goal with |- ?gg => idtac "AJ10" gg end ]
| first [ vm_compute; reflexivity | apply ret_ok_even; vm_compute; reflexivity | match goal with |- ?gg => idtac "AJ11" gg end ]
| first [ rewrite unsigned_lit_small by (clear; lia); clear; lia | idtac "AJ12" ]
| first [ apply achain_low; unfold s0Z; rewrite R8, E10, unsigned_lit_small by (clear - Ha4096 Haceil C1; lia); clear - Haceil; lia | match goal with |- ?gg => idtac "AJ13" gg end ]
| intros HPRE1; eapply SRr_mono;
[ pose proof (IHl d' ly S W (ms_regs ms) (ms_mem ms) mdc [] ((a, NODE_SIZE) :: tree_blocks r ++ rest) Hhl HPRE1) as CALL;
unfold cfg_at, apost_base in CALL; cbn [ss_pc]; change (w64 A_free_decision_tree) with (Z_to_bv 64 545512) in CALL;
apply CALL; clear CALL;
[ first [ unfold raZ; rewrite R1; cbn [spine map]; rewrite unsigned_lit_small by (clear; lia); vm_compute; tauto | match goal with |- ?gg => idtac "CA2" gg end ]
| first [ rewrite R10, E32; reflexivity | match goal with |- ?gg => idtac "CA5" gg end ]
| first [ exact Hatl1 | match goal with |- ?gg => idtac "CA9" gg end ]
| first [ exact HPl | match goal with |- ?gg => idtac "CA12" gg end ]
| first [ fold EVl; eapply bud_ok_mono; [exact Hev | clear - HEVl0 HEVr0; lia ..] | match goal with |- ?gg => idtac "CA21" gg end ] ]
| cbv beta; intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJc & HPc & Hpost);
exists ly4, S4, regs4, mem4, md4; split; [rewrite R1; reflexivity|]; split; [exact HJc|];
split; [exact HPc|]; exact Hpost ]
| first [ intros x Hx; left; split;
[ destruct (inFP_ablocks_fp_inv _ x Hx) as (pb & nb & Hpb & Hab); replace x with (pb + (x - pb)) by (clear; lia);
apply (inFP_ablocks_fp _ pb nb (x - pb)); [cbn [tree_blocks]; right; apply in_app_iff; left; exact Hpb | clear - Hab; lia]
| destruct (inFP_ablocks_fp_inv _ x Hx) as (pb & nb & Hpb & Hab); exists pb, nb; split; [apply Hsub; apply in_app_iff; left; exact Hpb | exact Hab] ]
| match goal with |- ?g => idtac "AJ15" g end ] ]
| ] end end.
clear HJ SHOK R2 R10 R3 R4 R1 R8.
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HJc & HP2 & HPerm2 & Hb2).
replace (spZ regs + -32) with (spZ regs - 32) in HJc by (clear; lia).
pose proof (proj1 HJ) as HAR2.
destruct (al_const _ _ LAWS _ _ _ _ _ HARc) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR2) as (Kcell2 & _ & Kgot2 & _). rewrite HBgot, HBcell in Kgot2. rewrite HBcell in Kcell2.
assert (Hina2 : In (a, NODE_SIZE) (ablocks B ly2 S2)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm2|]. left. reflexivity. }
assert (Hsubr2 : forall x, In x (tree_blocks r) -> In x (ablocks B ly2 S2)).
{ intros x Hx. eapply Permutation_in; [apply Permutation_sym; exact HPerm2|]. right. apply in_app_iff. left. exact Hx. }
assert (KC1 : forall b sz, In (b, sz) (tree_blocks r) -> rg_blk_kept (w_H W) (w_H W2) (ms_mem msB) mem2 b (req_size sz)).
{ intros b sz Hb. apply (rg_blk_kept_call B _ _ _ _ _ _ _ _ _ _ _ _ _ _ b sz HJc);
[apply Hsub; apply in_app_iff; right; exact Hb | exact (Hsubr2 _ Hb) |].
intros i Hi Hin. destruct (inFP_ablocks_fp_inv _ _ Hin) as (pb & nb & Hpb & Hab).
pose proof (rg_sep_app_in B LAWS ly S W mem md _ _ (pb, nb) (b, sz) HAR HPl Hpb
ltac:(right; apply in_app_iff; left; exact Hb)) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. clear - Hd Hi Hab. lia. }
lazymatch type of HS with st_ok _ ?Ex _ _ =>
jafter_call_keep HS 48%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2; 3]%nat HS2;
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end;
[ cbn [ms_mem restrict]; repeat apply Forall_cons; [| | | | apply Forall_nil];
[ eapply (region_kept_stack_sub trbsegs B); [exact HJc | exact HJ | rewrite ?ew_ewset_other by (cbv; lia); exact Usp | clear; lia | clear - HSTK; lia | clear; lia | clear; lia | clear; lia]
| apply (region_kept_val trbsegs Ex _ _ A_GOT_shadow 8 A_shadow_glob);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot2) | lia]
| apply (region_kept_val trbsegs Ex _ _ A_shadow_glob 8 SHADOW_OFF);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell2) | lia]
| eapply (region_kept_block_sub trbsegs B); [exact HJc | rewrite ?ew_ewset_other by (cbv; lia); rewrite E10; apply unsigned_lit_small; clear - Ha4096 Haceil C1; lia | exact Hina | exact Hina2
| clear; lia | change (req_size NODE_SIZE) with 56; unfold NODE_SIZE; clear; lia | clear; lia | ];
intros x Hx Hin; destruct (inFP_ablocks_fp_inv _ x Hin) as (pb & nb & Hpb & Hab);
pose proof (rg_sep_head_in B LAWS ly S W mem md (a, NODE_SIZE) _ (pb, nb) HAR HPerm ltac:(apply in_app_iff; left; exact Hpb)) as Hd;
unfold zdisjoint, block_rng in Hd; cbn [fst snd] in Hd; change (req_size NODE_SIZE) with 56 in Hd; unfold NODE_SIZE in Hx; clear - Hd Hx Hab; lia ]
| ] end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok _ (havoc ?Ex 48 ?lh) _ _ =>
remember (havoc Ex 48 lh) as E2' eqn:HE2' in HS;
assert (OLD2 : forall k, (k < 36)%nat -> ew E2' k = ew E k)
by (intros k Hk; rewrite HE2'; rewrite YO3v.ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; reflexivity);
assert (HAE2 : env_agree 32 (Ereg regs (fdt_extra (troot l) (troot r))) E2')
by (rewrite HE2'; apply env_agree_havoc_ge; [cbv; lia | env_agree_chain HAE]);
clear HE2' end.
assert (F1 : ew E2' 1 = getr regs 1) by (rewrite OLD2 by (cbv; lia); exact E1).
assert (F3 : ew E2' 3 = getr regs 3) by (rewrite OLD2 by (cbv; lia); exact E3).
assert (F4 : ew E2' 4 = getr regs 4) by (rewrite OLD2 by (cbv; lia); exact E4).
assert (F10 : ew E2' 10 = Z_to_bv 64 a) by (rewrite OLD2 by (cbv; lia); exact E10).
assert (F33 : ew E2' 33 = Z_to_bv 64 (troot r)) by (rewrite OLD2 by (cbv; lia); exact E33).
assert (F35 : ew E2' 35 = Z_to_bv 64 SB) by (rewrite OLD2 by (cbv; lia); exact E35).
assert (Usp2 : bv_unsigned (ew E2' 2) = spZ regs) by (rewrite OLD2 by (cbv; lia); exact Usp).
shok_auto_with SHOK Bx E2' (mrestrict (w_H W2) mem2) fdt_SH
ltac:(apply (shent_ok_of_block trbsegs B LAWS ly2 S2 W2 mem2 md2 E2' Bx 10 a NODE_SIZE 0 NODE_SIZE HAR2 Hina2);
[ unfold U, Bx; cbn [sv_denot]; rewrite F35, Z.add_0_r, Z_to_bv_bv_unsigned; rewrite unsigned_lit_small by (unfold SB; lia); reflexivity
| unfold U; cbn [sv_denot]; rewrite F10, Z.add_0_r, Z_to_bv_bv_unsigned; rewrite unsigned_lit_small by (clear - Ha4096 Haceil C1; lia); reflexivity
| lia | change (req_size NODE_SIZE) with 56; unfold NODE_SIZE; lia ]).
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK Bspan A_free_decision_tree.
{ eapply awr_ok_cons_stack; [reflexivity | exact Usp2 | cbn; clear - HSTK; lia | cbn; clear; lia |]. awr_ok_tac. }
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msC := msx) in * end.
rename HFr into HFr3. clear HF HG.
assert (KA3 : forall b sz, In (b, sz) (tree_blocks r) -> rg_blk_kept (w_H W2) (w_H W2) mem2 (ms_mem msC) b (req_size sz)).
{ intros b sz Hb. pose proof (Hsub _ ltac:(apply in_app_iff; right; exact Hb)) as Hbx.
destruct (al_blocks _ _ LAWS ly S W mem md b sz HAR Hbx) as (_ & Hb4096 & Hbceil & _).
lazymatch type of HFr3 with frame_of ?Ef ?rs _ _ => apply (rg_blk_kept_frame Ef rs (w_H W2) mem2 (ms_mem msC) b (req_size sz) HFr3) end.
intros x Hx. split; [clear - Hx Hb4096 Hbceil C1; lia|].
intros (rr & Hin & Hr). cbn [In] in Hin.
destruct Hin as [<- | [<- | [<- | [<- | []]]]];
cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr; try rewrite Usp2 in Hr;
clear - Hr Hx Hbceil Hceil Hslo Hstk0 HSTK; lia. }
assert (Hatr3 : tree_at trbsegs (mrestrict (w_H W2) (ms_mem msC)) r).
{ apply (rg_tree_at_kept (w_H W) (w_H W2) mem (ms_mem msC) r Hatr). intros b sz Hb.
eapply rg_blk_kept_trans; [eapply rg_blk_kept_trans; [eapply rg_blk_kept_trans; [apply KA1 | apply KA2] | apply KC1] | apply KA3];
first [exact Hb | apply in_app_iff; right; exact Hb]. }
assert (HPr : Permutation (ablocks B ly2 S2) (tree_blocks r ++ (a, NODE_SIZE) :: rest)).
{ eapply Permutation_trans; [exact HPerm2|]. apply Permutation_middle. }
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev2 & _).
pose proof (proj1 HJ) as HARc2.
lazymatch goal with |- SRr _ _ (mkCfg ?ms ?mdc) _ =>
lazymatch type of HS with st_ok _ ?Ex ?ssX _ =>
assert (UspY : bv_unsigned (ew Ex 2) = spZ regs) by (rewrite ?ew_ewset_other by (cbv; lia); exact Usp2);
rreg HS (2%bv : bv 5) R2; rreg HS (10%bv : bv 5) R10; rreg HS (3%bv : bv 5) R3; rreg HS (4%bv : bv 5) R4;
rreg HS (1%bv : bv 5) R1; rreg HS (8%bv : bv 5) R8;
eapply SRr_bind;
[ eapply (aj_call trbsegs B LAWS Hsegs W2 Ex ssX ms STK (spZ regs) _ ly S W mem md [] ly2 S2 mdc _
(FDT_STK (Z.of_nat d')) (ablocks_fp (tree_blocks r)) EVr (-32) (ew Ex 2) (Z_to_bv 64 0x8536c) []
(fun ly3 S3 W3 regs3 mem3 md3 => Permutation (ablocks B ly3 S3) ((a, NODE_SIZE) :: rest) /\ bud_le S2 S3 EVr 0 0 0) HS eq_refl HJ);
[ first [ exact (st_ok_restrict_reg trbsegs (w_H W2) Ex _ _ 2%bv HS) | match goal with |- ?gg => idtac "BJ1" gg end ]
| first [ reflexivity | idtac "BJ2" ]
| first [ exact UspY | idtac "BJ3" ]
| first [ reflexivity | idtac "BJ4" ]
| first [ lia | idtac "BJ5" ]
| first [ clear - HSTK1g; lia | idtac "BJ6" ]
| first [ clear - HSTK1; lia | match goal with |- ?gg => idtac "BJ7" gg end ]
| first [ rewrite R3, F3; exact Hgp | idtac "BJ8" ]
| first [ rewrite R4, F4; exact Htp | idtac "BJ9" ]
| first [ exact R1 | match goal with |- ?gg => idtac "BJ10" gg end ]
| first [ vm_compute; reflexivity | apply ret_ok_even; vm_compute; reflexivity | match goal with |- ?gg => idtac "BJ11" gg end ]
| first [ rewrite unsigned_lit_small by (clear; lia); clear; lia | idtac "BJ12" ]
| first [ apply achain_low; unfold s0Z; rewrite R8, F10, unsigned_lit_small by (clear - Ha4096 Haceil C1; lia); clear - Haceil; lia | match goal with |- ?gg => idtac "BJ13" gg end ]
| intros HPRE1; eapply SRr_mono;
[ pose proof (IHr d' ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdc [] ((a, NODE_SIZE) :: rest) Hhr HPRE1) as CALL;
unfold cfg_at, apost_base in CALL; cbn [ss_pc]; change (w64 A_free_decision_tree) with (Z_to_bv 64 545512) in CALL;
apply CALL; clear CALL;
[ first [ unfold raZ; rewrite R1; cbn [spine map]; rewrite unsigned_lit_small by (clear; lia); vm_compute; tauto | match goal with |- ?gg => idtac "CB2" gg end ]
| first [ rewrite R10, F33; reflexivity | match goal with |- ?gg => idtac "CB5" gg end ]
| first [ exact Hatr3 | match goal with |- ?gg => idtac "CB9" gg end ]
| first [ exact HPr | match goal with |- ?gg => idtac "CB12" gg end ]
| first [ fold EVr; eapply (bud_ok_at S S2 _ _ _ _ _ _ _ _ _ _ _ _ Hev Hb2); clear - HEVl0 HEVr0; lia | match goal with |- ?gg => idtac "CB21" gg end ] ]
| cbv beta; intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJc2 & HPc & Hpost);
exists ly4, S4, regs4, mem4, md4; split; [rewrite R1; reflexivity|]; split; [exact HJc2|];
split; [exact HPc|]; exact Hpost ]
| first [ intros x Hx; left; split;
[ destruct (inFP_ablocks_fp_inv _ x Hx) as (pb & nb & Hpb & Hab); replace x with (pb + (x - pb)) by (clear; lia);
apply (inFP_ablocks_fp _ pb nb (x - pb)); [cbn [tree_blocks]; right; apply in_app_iff; right; exact Hpb | clear - Hab; lia]
| destruct (inFP_ablocks_fp_inv _ x Hx) as (pb & nb & Hpb & Hab); exists pb, nb; split; [exact (Hsubr2 _ Hpb) | exact Hab] ]
| match goal with |- ?g => idtac "BJ15" g end ] ]
| ] end end.
clear HJ SHOK R2 R10 R3 R4 R1 R8.
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ & HJc2 & HP3 & HPerm3 & Hb3).
pose proof (bud_le_trans _ _ _ _ _ _ _ _ _ _ _ Hb2 Hb3) as Hb23.
replace (spZ regs + -32) with (spZ regs - 32) in HJc2 by (clear; lia).
pose proof (proj1 HJ) as HAR3.
destruct (al_const _ _ LAWS _ _ _ _ _ HARc2) as (Kcell3a & _ & Kgot3a & _). rewrite HBgot, HBcell in Kgot3a. rewrite HBcell in Kcell3a.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR3) as (Kcell3 & _ & Kgot3 & _). rewrite HBgot, HBcell in Kgot3. rewrite HBcell in Kcell3.
assert (Hina3 : In (a, NODE_SIZE) (ablocks B ly3 S3)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]. left. reflexivity. }
lazymatch type of HS with st_ok _ ?Ex _ _ =>
jafter_call_keep HS 80%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0; 1; 2; 3]%nat HS3;
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end;
[ cbn [ms_mem restrict]; repeat apply Forall_cons; [| | | | apply Forall_nil];
[ eapply (region_kept_stack_sub trbsegs B); [exact HJc2 | exact HJ | rewrite ?ew_ewset_other by (cbv; lia); exact Usp2 | clear; lia | clear - HSTK; lia | clear; lia | clear; lia | clear; lia]
| apply (region_kept_val trbsegs Ex _ _ A_GOT_shadow 8 A_shadow_glob);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot3a) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot3) | lia]
| apply (region_kept_val trbsegs Ex _ _ A_shadow_glob 8 SHADOW_OFF);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell3a) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell3) | lia]
| eapply (region_kept_block_sub trbsegs B); [exact HJc2 | rewrite ?ew_ewset_other by (cbv; lia); rewrite F10; apply unsigned_lit_small; clear - Ha4096 Haceil C1; lia | exact Hina2 | exact Hina3
| clear; lia | change (req_size NODE_SIZE) with 56; unfold NODE_SIZE; clear; lia | clear; lia | ];
intros x Hx Hin; destruct (inFP_ablocks_fp_inv _ x Hin) as (pb & nb & Hpb & Hab);
pose proof (rg_sep_head_in B LAWS ly2 S2 W2 _ _ (a, NODE_SIZE) _ (pb, nb) HARc2 HPerm2 ltac:(apply in_app_iff; left; exact Hpb)) as Hd;
unfold zdisjoint, block_rng in Hd; cbn [fst snd] in Hd; change (req_size NODE_SIZE) with 56 in Hd; unfold NODE_SIZE in Hx; clear - Hd Hx Hab; lia ]
| ] end.
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
lazymatch type of HS with st_ok _ (havoc ?Ex 80 ?lh) _ _ =>
remember (havoc Ex 80 lh) as E3' eqn:HE3' in HS;
assert (OLD3 : forall k, (k < 36)%nat -> ew E3' k = ew E2' k)
by (intros k Hk; rewrite HE3'; rewrite YO3v.ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; reflexivity);
assert (HAE3 : env_agree 32 (Ereg regs (fdt_extra (troot l) (troot r))) E3')
by (rewrite HE3'; apply env_agree_havoc_ge; [cbv; lia | env_agree_chain HAE2]);
clear HE3' end.
assert (G1 : ew E3' 1 = getr regs 1) by (rewrite OLD3 by (cbv; lia); exact F1).
assert (G10 : ew E3' 10 = Z_to_bv 64 a) by (rewrite OLD3 by (cbv; lia); exact F10).
assert (G35 : ew E3' 35 = Z_to_bv 64 SB) by (rewrite OLD3 by (cbv; lia); exact F35).
assert (Usp3 : bv_unsigned (ew E3' 2) = spZ regs) by (rewrite OLD3 by (cbv; lia); exact Usp2).
shok_auto SHOK Bx E3' (mrestrict (w_H W3) mem3).
aj_run_tok trbtbl_lib_ok HS HJ SHOK Bspan.
{ eapply awr_ok_cons_stack; [reflexivity | exact Usp3 | cbn; clear - HSTK; lia | cbn; clear; lia |]. awr_ok_tac. }
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
rreg HS (10%bv : bv 5) R10. rreg HS (1%bv : bv 5) R1.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 340932 with (pc_wrap_free code) by (rewrite HBcode; reflexivity).
eapply (fdt_tail STK _ W ly S regs mem md ch a _ rest W3 _ _ ly3 S3 _ _ HPRE HSTK HU0);
[ apply (vev_lt_of_bud S S3 _ _ _ _ _ _ _ _ Hev Hb23); clear - HEVl0 HEVr0; lia
| eapply bud_le_mono; [exact Hb23 | clear - HEVl0 HEVr0; lia ..]
| exact HJ | clear; lia | exact HPerm3 | | | |].
+ intros i Hi. apply (inFP_ablocks_fp _ a NODE_SIZE i); [cbn [tree_blocks]; left; reflexivity | exact Hi].
+ eapply (aregs_preserved_of_st_ok trbsegs _ _ _ _ regs (fdt_extra (troot l) (troot r)) HS); [env_agree_chain HAE3 | vm_compute; reflexivity].
+ cbn [ms_regs]. rewrite R10, G10. reflexivity.
+ cbn [ms_regs]. rewrite R1, G1. reflexivity.
Qed.
End e.
End c.
