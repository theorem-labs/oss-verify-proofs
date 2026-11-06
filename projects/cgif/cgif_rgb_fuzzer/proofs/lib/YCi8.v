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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCfx YCe9 YCfu
YCi1 YCib YCia YChy.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YP14 YI08 YI0c YI0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition gp_pix_chunks (fmt : Z) : list YQ0b.chunk :=
[YQ0b.mkChunk 0 (CVal 1 (SOff 33 0)); YQ0b.mkChunk 1 (CVal 1 (SOff 34 0)); YQ0b.mkChunk 2 (CVal 1 (SOff 35 0))]
++ (if fmt =? 4 then [YQ0b.mkChunk 3 (CVal 1 (SOff 36 0))] else []).
Definition gp_mem (fmt : Z) : smem :=
[ stack_region 16; got_region; bcell_region 32; YQ0b.mkRegion (Some 10%nat) 0 fmt 0 0 (gp_pix_chunks fmt) ].
Definition gp_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 4096 140737479966720 0); (32%nat, mkAF SB SB 0);
(33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0); (36%nat, mkAF 0 255 0) ] [] [].
Definition ss_gp (fmt : Z) : sstate := mkSS A_getPixelVal (sr_set sr_atoms 11%bv (SLit fmt)) (gp_mem fmt) None gp_facts.
Definition gp_Bx : sv := SOff 32 0.
Definition gp_SH (fmt : Z) : list shent := [ mkSHE 10 0 fmt ].
Definition gp_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition gp_extra (c : colour) (a : Z) : list word := map (Z_to_bv 64) [SB; cR c; cG c; cB c; a].
End b.
Section d. Context {fx : YK11.FPState}.
Lemma U_pix_combine_b : forall E eA n33 n34 n35 (c : colour) A,
ew E n33 = Z_to_bv 64 (cR c) -> ew E n34 = Z_to_bv 64 (cG c) -> ew E n35 = Z_to_bv 64 (cB c) -> colour_ok c ->
U E eA = A * 2 ^ 24 -> 0 <= A < 256 ->
U E (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_OR eA (SAlu ALU_SLL (SOff n34 0) (SLit 8))) (SAlu ALU_SLL (SOff n35 0) (SLit 16))) (SOff n33 0))
= A * 2 ^ 24 + cB c * 2 ^ 16 + cG c * 2 ^ 8 + cR c.
Proof.
intros E eA n33 n34 n35 c A H33 H34 H35 (Rr & Rg & Rb) HA RA.
rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SLit, HA.
rewrite (U_atom E n33 (cR c) H33), (U_atom E n34 (cG c) H34), (U_atom E n35 (cB c) H35) by lia.
change (Z.land (zcanon 16) 63) with 16. change (Z.land (zcanon 8) 63) with 8.
rewrite !Z.shiftl_mul_pow2 by lia.
rewrite (zcanon_id (cB c * 2 ^ 16)), (zcanon_id (cG c * 2 ^ 8)) by (unfold M64; lia).
assert (L1 : Z.lor (A * 2 ^ 24) (cG c * 2 ^ 8) = (A * 2 ^ 16 + cG c) * 2 ^ 8).
{ replace (A * 2 ^ 24) with ((A * 2 ^ 16) * 2 ^ 8) by lia.
rewrite <- Z.shiftl_mul_pow2, <- (Z.shiftl_mul_pow2 (cG c)), <- (Z.shiftl_mul_pow2 (A * 2 ^ 16 + cG c)) by lia.
rewrite <- Z.shiftl_lor. f_equal. apply lor_low_disjoint; lia. }
rewrite L1. rewrite (zcanon_id ((A * 2 ^ 16 + cG c) * 2 ^ 8)) by (unfold M64; lia).
assert (L2 : Z.lor ((A * 2 ^ 16 + cG c) * 2 ^ 8) (cB c * 2 ^ 16) = ((A * 2 ^ 8 + cB c) * 2 ^ 8 + cG c) * 2 ^ 8).
{ replace (cB c * 2 ^ 16) with ((cB c * 2 ^ 8) * 2 ^ 8) by lia.
rewrite <- Z.shiftl_mul_pow2, <- (Z.shiftl_mul_pow2 (cB c * 2 ^ 8)), <- (Z.shiftl_mul_pow2 ((A * 2 ^ 8 + cB c) * 2 ^ 8 + cG c)) by lia.
rewrite <- Z.shiftl_lor. f_equal.
replace (A * 2 ^ 16 + cG c) with (Z.lor (A * 2 ^ 16) (cG c)) by (apply lor_low_disjoint; lia).
rewrite <- Z.lor_assoc, (Z.lor_comm (cG c)), Z.lor_assoc.
replace (Z.lor (A * 2 ^ 16) (cB c * 2 ^ 8)) with ((A * 2 ^ 8 + cB c) * 2 ^ 8).
2:{ replace (A * 2 ^ 16) with ((A * 2 ^ 8) * 2 ^ 8) by lia.
rewrite <- Z.shiftl_mul_pow2, <- (Z.shiftl_mul_pow2 (cB c)), <- (Z.shiftl_mul_pow2 (A * 2 ^ 8)) by lia.
rewrite <- Z.shiftl_lor. f_equal. symmetry. apply lor_low_disjoint; lia. }
apply lor_low_disjoint; lia. }
rewrite L2. rewrite (zcanon_id (((A * 2 ^ 8 + cB c) * 2 ^ 8 + cG c) * 2 ^ 8)) by (unfold M64; lia).
rewrite (lor_low_disjoint ((A * 2 ^ 8 + cB c) * 2 ^ 8 + cG c) (cR c) 8) by lia.
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma gp_denot_of_U : forall E v z, U E v = z -> sv_denot E v = Z_to_bv 64 z.
Proof. intros E v z H. rewrite <- H. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
End d.
Section f. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section GP.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Lemma gp_entry : forall W regs memc STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdc k (pb pm pd fmt : Z) (c : colour) (a o : Z),
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 pd -> getr regs 11 = w64 fmt ->
spZ regs = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 16 - o <= STK ->
In (pb, pm) (ablocks B lyc Sc) -> pb <= pd -> pd + fmt <= pb + pm ->
col3 trbsegs (mrestrict (w_H W) memc) pd c ->
(fmt = 3 /\ a = 0) \/ (fmt = 4 /\ mbyte trbsegs (mrestrict (w_H W) memc) (pd + 3) = Some (Z_to_bv 8 a) /\ 0 <= a < 256) ->
st_ok trbsegs (Ereg regs (gp_extra c a)) (ss_gp fmt) (restrict (w_H W) (mkst regs (Z_to_bv 64 A_getPixelVal) memc (seg_rom trbsegs)))
/\ sh_ok trbsegs gp_Bx (gp_SH fmt) (Ereg regs (gp_extra c a)) (mrestrict (w_H W) memc).
Proof.
intros W regs memc STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdc k pb pm pd fmt c a o HJ H10 H11 Hsp' Hal Hneg Hbud Hblk Hpb Hpe Hcol Hfmt.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pb pm HAR Hblk) as (_ & Hi4096 & Hiceil & Hih_ia & _ & _ & Hin0). pose proof (proj1 Hih_ia) as Hih.
pose proof (blk_off_img _ _ _ _ _ _ pb pm HAR Hblk) as Hih_img.
pose proof (req_size_pos pm ltac:(lia)) as [_ HrNi].
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
destruct Hcol as (C0 & C1' & C2' & (Rr & Rg & Rb)).
assert (Ra : 0 <= a < 256) by (destruct Hfmt as [[_ ->] | (_ & _ & Ra)]; lia).
assert (Rf : fmt = 3 \/ fmt = 4) by (destruct Hfmt as [[-> _] | (-> & _)]; [left | right]; reflexivity).
rewrite restrict_mkst_fx.
set (E := Ereg regs (gp_extra c a)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 pd) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (cR c)) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (cG c)) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (cB c)) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 a) by (subst E; exact (ew_Ereg_extra regs _ 4)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew E 10) = pd) by (rewrite E10; apply unsigned_lit_small; clear - Hi4096 Hiceil Hpb Hpe HrNi Rf C1; lia).
assert (BY : forall q v, mbyte trbsegs (mrestrict (w_H W) memc) (pd + q) = Some (Z_to_bv 8 v) -> 0 <= v < 256 -> 0 <= q < fmt ->
forall n, ew E n = Z_to_bv 64 v ->
YQ0b.chunk_ok trbsegs E (mrestrict (w_H W) memc) pd (YQ0b.mkChunk q (CVal 1 (SOff n 0)))).
{ intros q v Hb Rv Hq n Hn.
apply (chunk_ok_val trbsegs E _ pd q 1 _ v); [cbn [sv_denot]; rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
apply (val_mem_byte trbsegs); assumption. }
split.
- unfold ss_gp. apply (entry_st_ok_full trbsegs); change (Ereg regs _) with E.
+ apply regs_ok_pin; [apply regs_ok_Ereg | intros HH0; discriminate HH0 |].
rewrite H11. cbn [sv_denot]. reflexivity.
+ destruct Rf as [-> | ->]; vm_compute; reflexivity.
+ unfold gp_mem, stack_region, got_region, bcell_region. repeat apply Forall_cons; try apply Forall_nil.
* unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. rewrite Usp.
split; [clear - Hslo Hceil C1 Hstk0 Hsp' Hbud; lia|]. split; [clear - Hshi H47 Hsp' Hneg; lia|]. split; [|constructor].
intros q Hq. apply (apresent_writable trbsegs). apply Hpres. clear - Hq Hsp' Hneg Hbud. lia.
* unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. unfold A_GOT_shadow.
split; [lia|]. split; [lia|]. split; [intros q Hq; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 0xa3250) at 1.
apply (chunk_ok_val trbsegs _ _ 0 0xa3250 8 (SLit A_shadow_glob) A_shadow_glob); [reflexivity | unfold A_shadow_glob; zside | zside |].
exact (val_mem_of_rdword trbsegs (w_H W) memc _ _ Kgot).
* unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. unfold A_shadow_glob.
split; [lia|]. split; [lia|]. split; [intros q Hq; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 0xab278) at 1.
apply (chunk_ok_val trbsegs _ _ 0 0xab278 8 gp_Bx SB);
[cbn [sv_denot gp_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
exact (val_mem_of_rdword trbsegs (w_H W) memc _ _ Kcell).
* unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. rewrite U10.
split; [clear - Hi4096 Hpb; lia|]. split; [clear - Hiceil Hpe HrNi C1; lia|]. split; [intros q Hq; lia|].
unfold gp_pix_chunks. apply Forall_app. split.
-- repeat apply Forall_cons; try apply Forall_nil.
++ apply (BY 0 (cR c)); [rewrite Z.add_0_r; exact C0 | exact Rr | clear - Rf; lia | exact E33].
++ apply (BY 1 (cG c)); [exact C1' | exact Rg | clear - Rf; lia | exact E34].
++ apply (BY 2 (cB c)); [exact C2' | exact Rb | clear - Rf; lia | exact E35].
-- destruct Hfmt as [[-> _] | (-> & Hb3 & _)]; cbn [Z.eqb Pos.eqb]; [apply Forall_nil|].
apply Forall_cons; [|apply Forall_nil]. apply (BY 3 a); [exact Hb3 | exact Ra | lia | exact E36].
+ apply pairwise_disjoint_of_extents. unfold gp_mem, stack_region, got_region, bcell_region, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. rewrite Usp, U10. unfold A_GOT_shadow, A_shadow_glob.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 Hstk0 Hiceil Hi4096 Hih Hih_img Hpb Hpe HrNi Rf Hsp' Hneg Hbud. clear. unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [gp_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, U10, E32, E33, E34, E35, E36, !unsigned_lit_small by (unfold SB; clear - Rr Rg Rb Ra C1; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
assert (Hspal : spZ regs mod 16 = 0) by (rewrite Hsp', Z.add_mod, Hsp0al, Hal by lia; reflexivity).
revert Hslo Hshi H47 Hceil Hspal C1 C3 Hstk0 Hiceil Hi4096 Hpb Hpe HrNi Rf Rr Rg Rb Ra Hsp' Hneg Hbud. clear.
unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, gp_SH. constructor; [|constructor].
apply (shent_ok_of_range trbsegs (w_H W) memc E gp_Bx 10 pd fmt pd 0 fmt).
+ apply (range_addressable_of_block trbsegs B LAWS lyc Sc W memc mdc pb pm _ _ HAR Hblk); clear - Hpb Hpe HrNi; lia.
+ unfold U, gp_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U10.
+ lia.
+ lia.
+ intros x Hx. revert Hx Hih_ia Hih_img Hiceil Hi4096 Hpb Hpe HrNi Rf C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia.
Qed.
Theorem trb_getPixelVal : tgpv_spec B.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pb pm pd fmt c op HJ Hraw Hra4 Hal16 Hlo Hhi G10 G11 Rf Hblk Hpb Hpe Hpix.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hpix as [Hcol Hfmt].
assert (Hfa : exists a, ((fmt = 3 /\ a = 0) \/ (fmt = 4 /\ mbyte trbsegs (mrestrict (w_H W) memc) (pd + 3) = Some (Z_to_bv 8 a) /\ 0 <= a < 256))
/\ (fmt = 3 -> op = true) /\ (fmt = 4 -> op = (128 <=? a))).
{ destruct Hfmt as [[-> ->] | (-> & a & Hb & Ra & ->)].
- exists 0. split; [left; split; reflexivity|]. split; [reflexivity | intros X; discriminate X].
- exists a. split; [right; split; [reflexivity | split; assumption]|]. split; [intros X; discriminate X | reflexivity]. }
destruct Hfa as (a & Hfa & Hop3 & Hop4).
assert (Ra : 0 <= a < 256) by (destruct Hfa as [[_ ->] | (_ & _ & Ra)]; lia).
set (o := spZ regs - sp0).
assert (Hsp' : spZ regs = sp0 + o) by (subst o; lia).
assert (Hneg : o <= 0) by (subst o; lia).
assert (Hal : o mod 16 = 0) by (subst o; rewrite Zminus_mod, Hal16, Hsp0al; reflexivity).
assert (Hbud : 16 - o <= STK) by (subst o; unfold TGPV_STK in Hlo; lia).
destruct (gp_entry W regs memc STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdc k pb pm pd fmt c a o HJ G10 G11 Hsp' Hal Hneg Hbud Hblk Hpb Hpe Hcol Hfa) as [HS SHOK].
remember (Ereg regs (gp_extra c a)) as E eqn:HE.
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 pd) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact G10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (cR c)) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (cG c)) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (cB c)) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 a) by (subst E; exact (ew_Ereg_extra regs _ 4)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (gp_extra c a)) E) by (rewrite HE; split; [intros m Hm; reflexivity | reflexivity]).
clear HE.
pose proof Hcol as (_ & _ & _ & Cok).
unfold cfg_at. change (w64 A_getPixelVal) with (Z_to_bv 64 A_getPixelVal).
assert (B10 : bv_unsigned (ew E 10) = pd).
{ rewrite E10. apply unsigned_lit_small.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pb pm HAR Hblk) as (_ & Hi4096 & Hiceil & _). pose proof (req_size_pos pm ltac:(destruct (al_blocks _ _ LAWS _ _ _ _ _ pb pm HAR Hblk) as (_ & _ & _ & _ & _ & _ & X); lia)) as [_ HrNi].
clear - Hi4096 Hiceil HrNi Hpb Hpe Rf C1. lia. }
assert (AG : forall m, (m < 33)%nat -> ew E m = ew E m) by (intros; reflexivity).
set (Zs0 := fun x : Z => sp0 + o - 16 <= x < sp0 + o).
destruct Rf as [-> | ->].
-
aj_run_tok trbtbl_lib_ok HS HJ SHOK gp_Bspan.
{ awrRD Usp E10. }
keStep HF HFr HG KE PR Zs0 Usp B10 Hsp'.
rreg HS (1%bv : bv 5) R1.
lazymatch type of HS with st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
assert (R10 : getr (ms_regs ms) 10 = w64 (pixel_word c op));
[ refine (eq_trans (st_ok_restrict_reg segs Hh Ex ss ms 10%bv HS) _);
lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end;
apply gp_denot_of_U;
rewrite (U_pix_combine_b Ex (SLit 4278190080) 33 34 35 c 255 ltac:(enorm; exact E33) ltac:(enorm; exact E34) ltac:(enorm; exact E35) Cok ltac:(rewrite U_SLit; vm_compute; reflexivity) ltac:(lia));
rewrite (Hop3 eq_refl); unfold pixel_word; lia
| ] end.
eapply (SRr_ret_at trbsegs trbtbl_lib trbtbl_lib_ok Hwx W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. split; [reflexivity|].
lazymatch goal with |- exists r2 m2 d2, {| cfg_ms := mkst (ms_regs ?msF) _ (ms_mem _) _; cfg_model := ?dd |} = _ /\ _ =>
exists (ms_regs msF), (ms_mem msF), dd end.
split. { cbn [ms_regs]. rewrite R1. enorm. agnorm. rewrite E1, Hraw. reflexivity. }
split. { apply (ajournal_materialize trbsegs B LAWS Hsegs). exact HJ. }
split. { apply aregs_preserved_eqs; cregRD HS HAE. }
split. { exact R10. }
split. { intros x Hx Hn. apply (KE x Hx). subst Zs0; cbn beta. unfold TGPV_STK in Hn. clear - Hn Hsp'. lia. }
exact PR.
-
aj_run_tok trbtbl_lib_ok HS HJ SHOK gp_Bspan.
{ awrRD Usp E10. }
keStep HF HFr HG KE PR Zs0 Usp B10 Hsp'.
rreg HS (1%bv : bv 5) R1.
lazymatch type of HS with st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
assert (R10 : getr (ms_regs ms) 10 = w64 (pixel_word c op));
[ refine (eq_trans (st_ok_restrict_reg segs Hh Ex ss ms 10%bv HS) _);
lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end;
apply gp_denot_of_U;
rewrite (U_pix_combine_b Ex (SAlu ALU_SLL (SAluw ALU_SRL (SExt true 8 (SOff 36 0)) (SLit 24)) (SLit 24)) 33 34 35 c (alpha8 a) ltac:(enorm; exact E33) ltac:(enorm; exact E34) ltac:(enorm; exact E35) Cok
(U_alpha_sext8 Ex 36 a ltac:(enorm; exact E36) Ra) ltac:(unfold alpha8; destruct (128 <=? a); lia));
rewrite (Hop4 eq_refl); unfold pixel_word, alpha8; destruct (128 <=? a); lia
| ] end.
eapply (SRr_ret_at trbsegs trbtbl_lib trbtbl_lib_ok Hwx W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. split; [reflexivity|].
lazymatch goal with |- exists r2 m2 d2, {| cfg_ms := mkst (ms_regs ?msF) _ (ms_mem _) _; cfg_model := ?dd |} = _ /\ _ =>
exists (ms_regs msF), (ms_mem msF), dd end.
split. { cbn [ms_regs]. rewrite R1. enorm. agnorm. rewrite E1, Hraw. reflexivity. }
split. { apply (ajournal_materialize trbsegs B LAWS Hsegs). exact HJ. }
split. { apply aregs_preserved_eqs; cregRD HS HAE. }
split. { exact R10. }
split. { intros x Hx Hn. apply (KE x Hx). subst Zs0; cbn beta. unfold TGPV_STK in Hn. clear - Hn Hsp'. lia. }
exact PR.
Qed.
End GP.
End f.
