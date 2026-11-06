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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI20.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YF8z YC1d YC1a YC2o YC10 YC2p YC1b YC2u YC1z.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition A_stack_malloc_2 : Z := 0x3d03c.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition FLBx : sv := SOff 32 0.
Definition FLBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition fl_extra (s : cgif_st) (f : frame_st) : list word := map (Z_to_bv 64) (SB :: tcgif_vals s ++ frame_vals f).
Definition fl_g_region : YQ0b.region := YQ0b.mkRegion (Some 10%nat) 0 CGIF_SIZE 0 0 (obj_chunks_gen LAY_CGIF 33 []).
Definition fl_cur_region : YQ0b.region := YQ0b.mkRegion (Some 11%nat) 0 FRAME_SIZE 20 24 (obj_chunks_gen LAY_Frame 50 []).
Definition fl_regions0 : smem :=
[ stack_region 384; got_region; bcell_region 32; uar_got_region; uar_cell_region; fl_g_region; fl_cur_region ].
Definition fl_atoms0 : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, HPTR 4); (11%nat, HPTR 4); (32%nat, mkAF SB SB 0);
(36%nat, mkAF 0 (2^64 - 1) 0); (38%nat, mkAF 0 (2^32 - 1) 0); (39%nat, mkAF 0 (2^32 - 1) 0);
(40%nat, mkAF 1 65535 0); (41%nat, mkAF 1 65535 0); (42%nat, mkAF 0 65535 0); (43%nat, mkAF 0 65535 0);
(46%nat, HPTR 4); (48%nat, mkAF 0 (2^32 - 1) 0); (49%nat, mkAF 0 (2^32 - 1) 0);
(50%nat, mkAF 0 (2^64 - 1) 0); (51%nat, HPTR 4); (52%nat, mkAF 0 (2^32 - 1) 0); (53%nat, mkAF 0 (2^32 - 1) 0);
(54%nat, mkAF 0 65535 0); (55%nat, mkAF 0 65535 0); (56%nat, mkAF 0 255 0); (57%nat, mkAF 0 255 0); (58%nat, mkAF 0 255 0) ].
Definition ss_fl0 : sstate := mkSS A_flushFrame sr_atoms fl_regions0 None (mkFacts fl_atoms0 [] []).
Section FL.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Lemma fl_cblocks_in : forall g s N i f,
nth_error (cg_frames s) i = Some (Some f) ->
In (g, CGIF_SIZE) (cgif_blocks g s N) /\ In (cg_raw s, RAW_SIZE) (cgif_blocks g s N) /\
In (fr_ptr f, FRAME_SIZE) (cgif_blocks g s N) /\ In (fr_img f, N) (cgif_blocks g s N).
Proof.
intros g s N i f Hf.
assert (Hfi : In (Some f) (cg_frames s)) by (eapply nth_error_In; exact Hf).
unfold cgif_blocks. split; [left; reflexivity|]. split; [right; left; reflexivity|].
assert (Hfb : forall x, In x (frame_blocks N f) -> In x ((g, CGIF_SIZE) :: (cg_raw s, RAW_SIZE) :: pal_blocks s ++ frames_blocks N (cg_frames s))).
{ intros x Hx. right. right. apply in_app_iff. right. unfold frames_blocks. apply in_flat_map. exists (Some f). split; [exact Hfi | exact Hx]. }
split; [apply Hfb; left; reflexivity | apply Hfb; right; left; reflexivity].
Qed.
Lemma fl_blocks_in : forall ly S g s N i f rest,
Permutation (ablocks B ly S) (cgif_blocks g s N ++ rest) ->
nth_error (cg_frames s) i = Some (Some f) ->
In (g, CGIF_SIZE) (ablocks B ly S) /\ In (cg_raw s, RAW_SIZE) (ablocks B ly S) /\
In (fr_ptr f, FRAME_SIZE) (ablocks B ly S) /\ In (fr_img f, N) (ablocks B ly S).
Proof.
intros ly S g s N i f rest HP Hf.
assert (Hsub : forall x, In x (cgif_blocks g s N) -> In x (ablocks B ly S)).
{ intros x Hx. eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_app_iff. left. exact Hx. }
assert (Hfi : In (Some f) (cg_frames s)) by (eapply nth_error_In; exact Hf).
unfold cgif_blocks in Hsub.
split; [apply Hsub; left; reflexivity|]. split; [apply Hsub; right; left; reflexivity|].
assert (Hfb : forall x, In x (frame_blocks N f) -> In x (ablocks B ly S)).
{ intros x Hx. apply Hsub. right. right. apply in_app_iff. right. unfold frames_blocks. apply in_flat_map. exists (Some f). split; [exact Hfi | exact Hx]. }
split; [apply Hfb; left; reflexivity | apply Hfb; right; left; reflexivity].
Qed.
Lemma fl_entry : forall W ly S regs mem md ch g s N i f rest,
afn_pre trasegs B TFLUSH_STK ly S W regs mem md ch ->
getr regs 10 = w64 g ->
tcgif_at (mrestrict (w_H W) mem) g s -> cgif_wf s N ->
nth_error (cg_frames s) i = Some (Some f) ->
getr regs 11 = w64 (fr_ptr f) ->
Permutation (ablocks B ly S) (cgif_blocks g s N ++ rest) ->
st_ok trasegs (Ereg regs (fl_extra s f)) ss_fl0
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_flushFrame) mem (seg_rom trasegs))).
Proof.
intros W ly S regs mem md ch g s N i f rest HPRE H10 HAT HWF Hf H11 HPerm.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : TFLUSH_STK = 17440) by reflexivity.
destruct (fl_blocks_in ly S g s N i f rest HPerm Hf) as (Hing & Hraw_in & Hcur_in & Himg_in).
destruct HAT as (Og & Oraw & Ofr).
assert (Hfi : In (Some f) (cg_frames s)) by (eapply nth_error_In; exact Hf).
pose proof (Ofr f Hfi) as Oc.
destruct HWF as (Hlen3 & HW1 & HH1 & HN & HNle & Hngp & Hih & Hfwf).
destruct (al_blocks _ _ LAWS ly S W mem md g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
destruct (al_blocks _ _ LAWS ly S W mem md (fr_ptr f) FRAME_SIZE HAR Hcur_in) as (Hc16 & Hc4096 & Hcceil & Hcrh_ia & Hcpres & _). pose proof (proj1 Hcrh_ia) as Hcrh.
pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR Hcur_in) as Hcrh_img.
destruct (al_blocks _ _ LAWS ly S W mem md (fr_img f) N HAR Himg_in) as (Hi16 & Hi4096 & Hiceil & Hirh_ia & _ & _). pose proof (proj1 Hirh_ia) as Hirh.
pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR Himg_in) as Hirh_img.
destruct (al_blocks _ _ LAWS ly S W mem md (cg_raw s) RAW_SIZE HAR Hraw_in) as (Hr16 & Hr4096 & Hrceil & Hrh_ia & _ & _). pose proof (proj1 Hrh_ia) as Hrh.
pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR Hraw_in) as Hrh_img.
change (req_size CGIF_SIZE) with 96 in *. change (req_size RAW_SIZE) with 48 in *. change (req_size FRAME_SIZE) with 40 in *.
assert (Hqi : 1 <= req_size N) by (unfold req_size; destruct (Z.eqb_spec N 0); lia).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite HBguar, HBuar in Kguar. rewrite HBuar in Kuar.
pose proof (sep_blocks trasegs _ LAWS ly S _ _ _ g CGIF_SIZE (fr_ptr f) FRAME_SIZE HAR Hing Hcur_in ltac:(unfold CGIF_SIZE, FRAME_SIZE; intros X; injection X; lia)) as Sgc.
unfold zdisjoint, block_rng in Sgc. cbn [fst snd] in Sgc. change (req_size CGIF_SIZE) with 96 in Sgc. change (req_size FRAME_SIZE) with 40 in Sgc.
pose proof Og as Og'. cbn [obj_at LAY_CGIF tcgif_vals] in Og'.
destruct Og' as ([_ R0] & [_ R1] & [_ R2] & [_ R3] & [_ R4] & [_ R5] & [_ R6] & [_ R7] & [_ R8] & [_ R9] & [_ R10] & [_ R11] & [_ R12] & [_ R13] & [_ R14] & [_ R15] & [_ R16] & _).
cbn [fst snd N.to_nat Z.of_N] in R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11, R12, R13, R14, R15, R16.
pose proof Oc as Oc'. cbn [obj_at LAY_Frame LAY_FrameConfig frame_vals app] in Oc'.
destruct Oc' as ([_ Q0] & [_ Q1] & [_ Q2] & [_ Q3] & [_ Q4] & [_ Q5] & [_ Q6] & [_ Q7] & [_ Q8] & _).
cbn [fst snd N.to_nat Z.of_N] in Q0, Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8.
change (2 ^ (8 * 8)) with (2 ^ 64) in *. change (2 ^ (8 * 4)) with (2 ^ 32) in *. change (2 ^ (8 * 2)) with 65536 in *. change (2 ^ (8 * 1)) with 256 in *.
rewrite restrict_mkst_fx.
set (E := Ereg regs (fl_extra s f)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 g) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 (fr_ptr f)) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (EX : forall j, ew E (32 + j) = nth j (fl_extra s f) (Z_to_bv 64 0)) by (intros j; subst E; apply ew_Ereg_extra).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (exact (EX 0%nat)).
assert (EG : forall j v, nth_error (tcgif_vals s) j = Some v -> ew E (33 + j) = Z_to_bv 64 v).
{ intros j v Hj. pose proof (nth_error_nth _ j 0 Hj) as Hn.
assert (Hlt : (j < length (tcgif_vals s))%nat).
{ destruct (Nat.lt_ge_cases j (length (tcgif_vals s))) as [Hl|Hge]; [exact Hl|]. rewrite (proj2 (nth_error_None _ _) Hge) in Hj. discriminate. }
replace (33 + j)%nat with (32 + Datatypes.S j)%nat by lia. rewrite (EX (Datatypes.S j)). unfold fl_extra.
rewrite map_nth. cbn [nth]. rewrite app_nth1 by exact Hlt. rewrite Hn. reflexivity. }
assert (EF : forall j v, nth_error (frame_vals f) j = Some v -> ew E (50 + j) = Z_to_bv 64 v).
{ intros j v Hj. pose proof (nth_error_nth _ j 0 Hj) as Hn.
replace (50 + j)%nat with (32 + Datatypes.S (17 + j))%nat by lia. rewrite (EX (Datatypes.S (17 + j))%nat). unfold fl_extra.
rewrite map_nth. cbn [nth]. rewrite app_nth2 by (cbn; lia). change (length (tcgif_vals s)) with 17%nat.
replace (17 + j - 17)%nat with j by lia. rewrite Hn. reflexivity. }
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold ss_fl0. apply (entry_st_ok_full trasegs); change (Ereg regs (fl_extra s f)) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold fl_regions0, stack_region, got_region, bcell_region, uar_got_region, uar_cell_region.
repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. rewrite Usp.
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable trasegs). apply Hpres. lia.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. unfold A_GOT_shadow.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 663904) at 1.
apply (chunk_ok_val trasegs E _ 0 663904 8 (SLit A_shadow_glob) A_shadow_glob); [reflexivity | unfold A_shadow_glob; zside | zside |].
exact (val_mem_of_rdword trasegs (w_H W) mem _ _ Kgot).
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. unfold A_shadow_glob.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 696760) at 1.
apply (chunk_ok_val trasegs E _ 0 696760 8 (SOff 32 0) SB);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
exact (val_mem_of_rdword trasegs (w_H W) mem _ _ Kcell).
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. unfold A_GOT_uar.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 663992) at 1.
apply (chunk_ok_val trasegs E _ 0 663992 8 (SLit A_uar_glob) A_uar_glob); [reflexivity | unfold A_uar_glob; zside | zside |].
exact (val_mem_of_rdword trasegs (w_H W) mem _ _ Kguar).
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. unfold A_uar_glob.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 696768) at 1.
apply (chunk_ok_val trasegs E _ 0 696768 4 (SLit 1) 1); [reflexivity | zside | zside |].
exact (val_mem_of_rd32 trasegs (w_H W) mem _ _ Kuar).
+ unfold fl_g_region. apply (region_ok_obj_gen trasegs E _ 10 g CGIF_SIZE 0 0 LAY_CGIF (tcgif_vals s) 33 []);
[rewrite E10; apply unsigned_lit_small; lia | lia | unfold CGIF_SIZE; lia | exact Og | vm_compute; reflexivity
| intros j v Hj; exact (EG j v Hj) | intros j z Hj; destruct j; discriminate | intros o Ho; lia].
+ unfold fl_cur_region. apply (region_ok_obj_gen trasegs E _ 11 (fr_ptr f) FRAME_SIZE 20 24 LAY_Frame (frame_vals f) 50 []);
[rewrite E11; apply unsigned_lit_small; lia | lia | unfold FRAME_SIZE; lia | exact Oc | vm_compute; reflexivity
| intros j v Hj; exact (EF j v Hj) | intros j z Hj; destruct j; discriminate
| intros o Ho; apply (apresent_writable trasegs); apply (proj1 (Hcpres (fr_ptr f + o) ltac:(lia)))].
- apply pairwise_disjoint_of_extents.
unfold fl_regions0, stack_region, got_region, bcell_region, uar_got_region, uar_cell_region, fl_g_region, fl_cur_region, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi]. rewrite (VB 10%nat g E10), (VB 11%nat (fr_ptr f) E11) by lia. cbn [base_val]. rewrite Usp.
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, CGIF_SIZE, FRAME_SIZE.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hgceil Hgh Hgh_img Hg4096 Hcceil Hcrh Hcrh_img Hc4096 Sgc C1 C3 FFS Hstk0. clear. unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok fl_atoms0]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
pose proof (EG 3%nat _ eq_refl) as E36. pose proof (EG 5%nat _ eq_refl) as E38. pose proof (EG 6%nat _ eq_refl) as E39.
pose proof (EG 7%nat _ eq_refl) as E40. pose proof (EG 8%nat _ eq_refl) as E41. pose proof (EG 9%nat _ eq_refl) as E42.
pose proof (EG 10%nat _ eq_refl) as E43. pose proof (EG 13%nat _ eq_refl) as E46. pose proof (EG 15%nat _ eq_refl) as E48.
pose proof (EG 16%nat _ eq_refl) as E49.
pose proof (EF 0%nat _ eq_refl) as E50. pose proof (EF 1%nat _ eq_refl) as E51. pose proof (EF 2%nat _ eq_refl) as E52.
pose proof (EF 3%nat _ eq_refl) as E53. pose proof (EF 4%nat _ eq_refl) as E54. pose proof (EF 5%nat _ eq_refl) as E55.
pose proof (EF 6%nat _ eq_refl) as E56. pose proof (EF 7%nat _ eq_refl) as E57. pose proof (EF 8%nat _ eq_refl) as E58.
cbn [Nat.add] in E36, E38, E39, E40, E41, E42, E43, E46, E48, E49, E50, E51, E52, E53, E54, E55, E56, E57, E58.
rewrite Usp, E10, E11, E32, E36, E38, E39, E40, E41, E42, E43, E46, E48, E49, E50, E51, E52, E53, E54, E55, E56, E57, E58.
rewrite !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hgceil Hgh Hgh_img Hg4096 Hg16 Hcceil Hcrh Hcrh_img Hc4096 Hc16 Hiceil Hirh Hirh_img Hi4096 Hi16 Hqi Hrceil Hrh Hrh_img Hr4096 Hr16
R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 Q0 Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 HW1 HH1 C1 C3 FFS Hstk0 Hal16. clear. unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros.
repeat match goal with |- _ /\ _ => split end; lia.
Qed.
End FL.
End a.
